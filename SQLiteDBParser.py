# -*- coding: utf-8 -*-
#-------------------------------------------------------------------------------
# Name:        SQLiteDBParser - Forensic SQLite Database Analyzer
# Purpose:     Parses a sqlite database and tries to restore deleted records
#              in unused pages, freespace and unallocated space.
#
# Author:      GrisoMG
#
# References:  n0fate: schema parser example https://github.com/n0fate/walitean
#              Jim Hung: cellparser https://github.com/NotionalLabs/SQLiteZer
#              Sho Nakatani (laysakura) handling of overflow pages https://github.com/laysakura/SQLiteDbVisualizer
#
# Limitations: sql command parser is not working 100% correctly
#              matching of deleted pages to tables only based on column count
#
#              output is not really nice
#              pointer maps are not handled correctly
#
# Requires:    Python 3
#
# Created:     19/08/2015
# License:     GPL v2.0
#-------------------------------------------------------------------------------

__author__ = 'grisomg'

from struct import unpack
from optparse import OptionParser, OptionGroup
import sys, tempfile, operator, string

VERSION = '0.9'
BUILD = '20151112'

GPLNOTICE = '   Copyright (C) 2015 GrisoMG\n\
    This program comes with ABSOLUTELY NO WARRANTY\n\
    This is free software, and you are welcome to redistribute it\n\
    under certain conditions'


JPGHEADER = b'\xff\xd8\xff\xe0'
JPGIDENT =  b'JFIF\0'
JPGHEADERLEN = 12

EXIFHEADER = b'\xff\xd8\xff\xe1'
EXIFIDENT = b'Exif\0'
EXIFHEADERLEN = 12

MA4HEADER = b'\x10\x00\x00\x00\x1c\x66\x74'
MA4HEADERLEN = 7

MOVHEADER = b'\x00\x00\x00\x1C\x66\x74\x79\x70\x6D\x70\x34\x32'
MOVHEADERLEN = 12

BPLISTHEADER = b'\x62\x70\x6C\x69\x73\x74'
BPLISTHEADERLEN = 6

MP3HEADER = b'\x49\x44\x33' #with ID3v2 container
MP3HEADERLEN = 3

SQLITE_SIGNATURE = b'SQLite format 3\x00'

INTERIOR_INDEX_BTREE_PAGE = 2
INTERIOR_TABLE_BTREE_PAGE = 5
LEAF_INDEX_BTREE_PAGE = 10
LEAF_TABLE_BTREE_PAGE = 13

INTERIOR_OFFSET = 12
LEAF_OFFSET = 8

sql_type = ('table', 'trigger', 'index', 'view')

class CellContent:
    LEFT_CHILD_PAGE_NUM = "left child page num"
    PAYLOAD_SIZE = "payload size"
    RID = "rid"
    PAYLOAD = "payload"
    OVERFLOW_PAGE_HEAD = "overflow page head"

#######################################################################################
#
# class SQLiteDBParser
#
#######################################################################################
class SQLiteDBParser:
    #sqlite database header first 100 bytes
    _dbhdrfrmt = '>16sHbbbbbbiiiiiiiiiiii20sii'
    _dbhdrkeys = ["signature", "pageSize", "write_version", "read_version", "unused_reserved_space", "maximum_embedded_payload_fraction",
                 "minimum_embedded_payload_fraction", "leaf_payload_fraction", "file_change_counter", "in_header_database_size",
                 "first_freelist_trunk_page", "total_num_freelist_pages", "schema_cookie", "schema_format_number", "default_page_cache_size",
                 "largest_root_b_tree", "database_text_encoding", "user_version", "incremental_vacuum", "application_id", "reserved",
                 "version_valid_for_number", "sqlite_version_number"]

    #header of a btree table
    _lbtreefrmt = '>bhhhb'  #b-tree header for leaf b-tree pages
    _ibtreefrmt = '>I'      #additional for interior b-tree pages
    _btreehdrkeys  = ['pageByte', 'fbOffset', 'cellQty', 'cellOffset', 'freebytes', 'rmpointer']

    #header of pointer map
    _ptrmapfrmt = '>bI'
    _ptrmaphdrkeys = ['pageType', 'pageNr']

    def __init__(self, options):

        self.opt = {'sqlitedb': '', 'debug':False, 'bin2out':False, 'bin2file':False, 'freespace':False, 'unallocated':False, 'deleted':False}
        self.opt['sqlitedb'] = options.infile
        self.opt['debug'] = options.debug
        self.opt['bin2out'] = options.bin2out
        self.opt['bin2file'] = options.bin2file
        self.opt['freespace'] = options.freespace
        self.opt['unallocated'] = options.unallocated
        self.opt['deleted'] = options.deleted
        self.opt['verbose'] = False # future use :-)

        self.data = b''
        self.pageOffsets = []
        self.dbInfo = dict()
        self.dbHeaderDict = dict()
        self.ptrMap = list()
        self.dbSchema = {}
        self.dbPages = []
        self.lPagesWithoutRoot = []
        self.overflowpages = []

        if self.opt['bin2file']:
            self.tmpdir = self._makeTmpDir()

        # 1. read db file, parse header, check if valid sqlite database, parse schema, get page offsets
        self._readDBFile()
        self._parseDBHeader()
        if self.isSqliteDB() == False:
            return None

#        self.dbSchema = self._parseDBSchema(self.data[:self.dbHeaderDict["pageSize"]])
        self._getPageOffsets()

        # 2. read all pages
        self._readallDBPages()
        self._markOverflowPages()
        self.dbSchema = self._parseDBSchema(1)
        self._setSchemaForRootPages()

        # 3. are all leaf pages assigned to a root page? if not try to find a mapping root page by mapping schema
        self._lPagesWithoutRoot()

    def _markOverflowPages(self):

        for page in self.dbPages:
            if self.dbPages[page]['pageNr'] in self.overflowpages:
                self.dbPages[page]['pageType'] = 'Overflow Page'

    def isSqliteDB(self):

        if self.dbHeaderDict["signature"] == SQLITE_SIGNATURE:
            return True
        else:
            return False

    def isRootPage(self, dbpage):
        try:
            if dbpage["isRootPage"] == True:
                return True
        except:
            return False

    def hasFreespace(self, dbpage):
        try:
            if dbpage["freespace"].__len__() > 0:
                return True
        except:
            return False

    def hasUnallocated(self, dbpage):
        try:
            if dbpage["unallocated"].__len__() > 0:
                return True
        except:
            return False

    def hasCelldata(self, dbpage):
        try:
            if dbpage["celldata"].__len__() > 0:
                return True
        except:
            return False

    def hasDeleted(self, dbpage):
        try:
            if dbpage["deletedpages"].__len__() > 0:
                return True
        except:
            return False

    def hasLeafPages(self, dbpage):
        try:
            if dbpage["leafpages"].__len__() > 0:
                return True
        except:
            return False

    def hasPtrMap(self):
        ret = False
        if self.ptrMap.__len__() > 0:
            ret = True
        return ret

    def _lPagesWithoutRoot(self):
        for page in self.dbPages:
            schemalist = list()
            if self.dbPages[page]["pageHeader"]["pageByte"] == LEAF_TABLE_BTREE_PAGE:
                if self._findLPageinRPage(self.dbPages[page]["pageNr"]) == -1:
                    if self.dbPages[page]["pageHeader"]["cellQty"] > 0:
                        schemalist = self._findMatchingSchema(self.dbPages[page]["celldata"])
                        #add page to leafpages for root pages in schemalist
                        self._addLeafPage2RootPage(self.dbPages[page]["pageNr"], schemalist)

    def _addLeafPage2RootPage(self, pageNr, schemalist):

        for rootNr in schemalist:
            try:
                self.dbPages[rootNr]["deletedpages"].append(pageNr)
            except:
                try:
                    self.dbPages[rootNr]["deletedpages"] = list()
                    self.dbPages[rootNr]["deletedpages"].append(pageNr)
                except:
                    pass

    def _findMatchingSchema(self, celldata):
        #compare number of columns with schema of tables
        #col type are not checked at the moment ;-(
        num_of_cols = celldata[0].__len__()
        possibleschemalist = list()
        for schema in self.dbSchema:
            if not self.dbSchema[schema]['type'] == 'table':
                continue
            if num_of_cols == self.dbSchema[schema]["schema"].__len__():
                possibleschemalist.append(self.dbSchema[schema]["rootpage"])
        return possibleschemalist

    def _findLPageinRPage(self, pageNr):
        for page in self.dbPages:
            if self.dbPages[page]["pageHeader"]["pageByte"] == INTERIOR_TABLE_BTREE_PAGE:
                try:
                    if pageNr in self.dbPages[page]["leafpages"]:
                        return self.dbPages[page]["pageNr"]
                except:
                    pass
        return -1

    def _findSQLCmd(self, buf):
        open = 0
        start = 0
        end = 0
        i = 0
        bindata = False

        buf = buf.replace('\n','')
        try:
            if chr(buf[0]):
                bindata = True
        except:
            bindata = False

        while i < buf.__len__():
            if not bindata:
                if buf[i] == '(':
                    if start == 0:
                        start = i
                    open += 1
                if buf[i] == ')':
                    open -= 1
                    if open == 0:
                        end = i
                        break
            else:
                if chr(buf[i]) == '(':
                    if start == 0:
                        start = i
                    open += 1
                if chr(buf[i]) == ')':
                    open -= 1
                    if open == 0:
                        end = i
                        break
            i += 1
        if end <= start:
            return "ERROR"
        else:
            return buf[start+1:end]

    def _setSchemaForRootPages(self):

        for table in self.dbSchema:
            if not isinstance(self.dbSchema[table]["rootpage"], int):
                continue
            if not self.dbSchema[table]['type'] == 'table':
                continue
            colheader = list()
            tblinfo = dict()
            for x in self.dbSchema[table]["schema"]:
                colheader.append(x[0])
            tblinfo[self.dbSchema[table]["name"]] = colheader

            self.dbPages[self.dbSchema[table]["rootpage"]]["schema"] = tblinfo
            self.dbPages[self.dbSchema[table]["rootpage"]]["isRootPage"] = True

    def _getSchemaForRootPage(self, rootpage):
        colheader = list()
        tblinfo = dict()
        for table in self.dbSchema:
            if self.dbSchema[table]["rootpage"] == rootpage:
                for x in self.dbSchema[table]["schema"]:
                    colheader.append(x[0])
                tblinfo[self.dbSchema[table]["name"]] = colheader
        return tblinfo

    def _getPageOffsets(self):

        for offset in range(0, len(self.data), self.dbHeaderDict["pageSize"]):
            self.pageOffsets.append(offset)

    def _lookUpTable(self, tbl_name):

        for table in self.dbSchema:
            if self.dbSchema[table]["name"] == tbl_name:
                return self.dbSchema[table]["rootpage"]
        return None

    def _readallDBPages(self):
        pageSize = self.dbHeaderDict["pageSize"]
        pageNr = 0

        pageDict = {}
        for offset in self.pageOffsets:
            dbpage = {}
            pageNr += 1

            dbpage = self._readDBPage(pageNr, offset)
            pageDict[pageNr] = dbpage
            self.dbPages = pageDict
            offset += pageSize

    def _readDBPage(self, pageNr, offset):

        pageSize = self.dbHeaderDict["pageSize"]
        pageHeader = []
        counter = 0
        dbpage = {}
        page = self.data[offset: offset + pageSize]

        if pageNr == 2 and self.dbHeaderDict["incremental_vacuum"] > 0:
            #in this case, the page is a pointer map
            self._readPointerMap(page)

        pageHeader = self._parsePageHeader(page, pageNr)
        dbpage["page"] = page
        dbpage["pageNr"] = pageNr
        dbpage["pageOffset"] = offset
        dbpage["pageHeader"] = pageHeader
        dbpage["isRootPage"] = False

        dbpage["celldata"] = list()
        dbpage["deleteddata"] = list()

        dbpage["fs_celldata"] = list()
        if dbpage["pageHeader"]["pageByte"] == INTERIOR_INDEX_BTREE_PAGE:
            dbpage["pageType"] = "interior index b-tree"
            if pageNr == 2:
                counter += 1
        elif dbpage["pageHeader"]["pageByte"] == INTERIOR_TABLE_BTREE_PAGE:
            dbpage["pageType"] = "interior table b-tree"
            if pageNr == 2:
                counter += 1
        elif dbpage["pageHeader"]["pageByte"] == LEAF_INDEX_BTREE_PAGE:
            dbpage["pageType"] = "leaf index b-tree"
        elif dbpage["pageHeader"]["pageByte"] == LEAF_TABLE_BTREE_PAGE:
            dbpage["pageType"] = "leaf table b-tree"
        elif pageNr == 2 and self.dbHeaderDict["incremental_vacuum"] > 0:
            dbpage["pageType"] = "pointer map"
        else:
            dbpage["pageType"] = "Unknown"
            if pageNr == 2 and (dbpage["pageType"] in (3,4)):
                counter += 1
        dbpage["cellPointer"] = self._readPageCellPointer(page, dbpage["pageHeader"], pageNr)

#            if pageNr > 1 and dbpage["pageHeader"]["pageByte"] == INTERIOR_TABLE_BTREE_PAGE:
        if dbpage["pageHeader"]["pageByte"] == INTERIOR_TABLE_BTREE_PAGE:
            dbpage["leafpages"] = self._readLeafPageList(dbpage, offset)
            dbpage["hasLeafPages"] = True

#            if (dbpage["pageHeader"]["pageByte"] == LEAF_TABLE_BTREE_PAGE) and (dbpage["pageHeader"]["cellQty"] > 0):
        if ((dbpage["pageHeader"]["pageByte"] == LEAF_TABLE_BTREE_PAGE) or (dbpage["pageHeader"]["pageByte"] == LEAF_INDEX_BTREE_PAGE) \
                    or (dbpage["pageHeader"]["pageByte"] == INTERIOR_TABLE_BTREE_PAGE) or (dbpage["pageHeader"]["pageByte"] == INTERIOR_INDEX_BTREE_PAGE)) and (dbpage["pageHeader"]["cellQty"] > 0):
            dbpage["celldata"] = self._readPageCells(dbpage, offset)

        dbpage["unallocated"] = self._readPageUnallocated(dbpage)
        dbpage["freespace"], dbpage["fs_celldata"] = self._readPageFreeSpace(dbpage)

        return dbpage

    def _readPageCells(self, dbpage, offset):
        celldatalist = list()
        for cp in range(0,(dbpage["pageHeader"]["cellQty"]*2),2):
            celldata = list()
            start = cp
            end = cp + 2
            cellp = unpack('>H', dbpage["cellPointer"][start:end])[0]
            cellstart = offset + cellp
            celldata, payloadlen = self._parseCell(self.data, cellstart, dbpage["pageHeader"]["pageByte"])
            celldatalist.append(celldata)

        return celldatalist

    def _readLeafPageList(self, dbpage, offset):
        leafpagelist = list()
        offset = offset
        for cp in range(0,(dbpage["pageHeader"]["cellQty"]*2),2):
            start = cp
            end = cp + 2
            cellp = unpack('>h', dbpage["cellPointer"][start:end])[0]
            cellstart = offset + cellp
            leftchildpointer = unpack('>L', self.data[cellstart:cellstart+4])[0]
            #key = _getVarIntOfs(data, offset+4)
            leafpagelist.append(leftchildpointer)
        leafpagelist.append(dbpage["pageHeader"]["rmpointer"])
        return leafpagelist

    def _readPageFreeSpace(self, dbpage):
        fbOffset = dbpage["pageHeader"]["fbOffset"]
        freeblocklist = list()
        fs_data = list()
        fs_celldata = list()
        #fs_record = ''
        rs_offset = 2
        while fbOffset > 0:
            try:
                start, size = unpack('>hh', dbpage["page"][fbOffset: fbOffset + 4])
                if size > 0:
                    freeblock = dbpage["page"][fbOffset: fbOffset + size]
                    fs_data, payloadlen  = self._parseFreeSpaceCell(freeblock, 4, dbpage["pageHeader"]["pageByte"])
                else:
                    freeblock = ''
                freeblocklist.append(freeblock)
                fs_celldata.append(fs_data)
                if (fbOffset != start) and (start > 0):
                    fbOffset = start
                else:
                    fbOffset = 0
                '''
                fbOffset = start
                '''
            except:
                fbOffset = 0
        return freeblocklist, fs_celldata

    def _parseFreeSpaceCell(self, data, offset, cellformat):
        '''
        Work in progress
        :rtype: list
        '''

        fs_celldata = list()
        #fs_record, payloadlen = self._parseCell(data, offset, cellformat)
        cellheader, payloadheaderlen, dataoffset, payloadlen, recordnum, payloadsizeincell, overflowpageoffset,overflowpagenum = self._parseLeafTableCellHeader(data, offset, freespace=True)
        payload = data[dataoffset:]
        if (overflowpagenum > 0) and (overflowpagenum is not None):
            payload += self._getoverflowdata(overflowpagenum)
        data = payload
        dataoffset = 0
        for field in cellheader:
            dataoffset = int(dataoffset)
            if field[0] == "NULL":
                fs_celldata.append(recordnum)
            elif field[0] == "ST_INT8":
                fs_celldata.append(ord(unpack(">c",data[dataoffset:dataoffset+1])[0]))
                dataoffset+=field[1]
            elif field[0] == "ST_INT16":
                fs_celldata.append(unpack(">h",data[dataoffset:dataoffset+2])[0])
                dataoffset+=field[1]
            elif field[0] == "ST_INT24":
                fs_celldata.append("-")
                dataoffset+=field[1]
            elif field[0] == "ST_INT32":
                fs_celldata.append(unpack(">i",data[dataoffset:dataoffset+4])[0])
                dataoffset+=field[1]
            elif field[0] == "ST_INT48":
                fs_celldata.append(unpack(">i",data[dataoffset:dataoffset+6])[0])
                dataoffset+=field[1]
                #fs_celldata.append("ST_INT48 - NOT IMPLEMENTED!") # NOT IMPLEMENTED YET!
                #dataoffset+=field[1]
            elif field[0] == "ST_INT64":
                fs_celldata.append(unpack(">q",data[dataoffset:dataoffset+8])[0])
                dataoffset+=8
            elif field[0] == "ST_FLOAT":
                fs_celldata.append(unpack(">d",data[dataoffset:dataoffset+8])[0])
                dataoffset+=8
            elif field[0] == "ST_C0":
                fs_celldata.append("-")
            elif field[0] == "ST_C1":
                fs_celldata.append("-")
            elif field[0] == "ST_BLOB":
                cell = data[dataoffset:dataoffset+int(field[1])]
                fs_celldata.append(cell)
                dataoffset+=field[1]
            elif field[0] == "ST_TEXT":
                try:
                    fs_celldata.append(data[dataoffset:dataoffset+int(field[1])].decode('UTF-8'))
                except:
                    try:
                        fs_celldata.append(str(data[dataoffset:dataoffset+int(field[1])]))
                    except:
                        pass

                dataoffset+=field[1]
            else:
                pass
                #print(field[0])

        return fs_celldata, payloadlen

    def _readPageUnallocated(self, dbpage):
        if dbpage["pageNr"] == 1 and dbpage["pageHeader"]["pageByte"] != INTERIOR_TABLE_BTREE_PAGE:
            start = 108 + dbpage["pageHeader"]["cellQty"] * 2
        elif dbpage["pageNr"] == 1 and dbpage["pageHeader"]["pageByte"] == INTERIOR_TABLE_BTREE_PAGE:
            start = 112 + dbpage["pageHeader"]["cellQty"] * 2
        elif dbpage["pageHeader"]["pageByte"] == INTERIOR_TABLE_BTREE_PAGE:
            start = 12 + dbpage["pageHeader"]["cellQty"] * 2
        else:
            start = 8 + dbpage["pageHeader"]["cellQty"] * 2

        end = dbpage["pageHeader"]["cellOffset"] - start
        return dbpage["page"][start:end]

    def _readPageCellPointer(self, page, pageHeader, pageNr):
        cellPointer = 0
        if pageHeader["cellQty"] > 0:
            if pageNr == 1 and pageHeader["pageByte"] != INTERIOR_TABLE_BTREE_PAGE:
                start = 108
            elif pageNr == 1 and pageHeader["pageByte"] == INTERIOR_TABLE_BTREE_PAGE:
                start = 112
            elif pageHeader["pageByte"] == INTERIOR_TABLE_BTREE_PAGE:
                start = 12
            else:
                start = 8
            end = start + (pageHeader["cellQty"] * 2)
            cellPointer = page[start:end]
        return cellPointer

    def _readPointerMap(self, page):
        ptrMapLen = 5
        offset = 0
        ptrmapdict = dict()
        counter = 0
        while offset < (self.dbHeaderDict["pageSize"]- ptrMapLen):
            hdr = unpack(self._ptrmapfrmt, page[offset:offset+ptrMapLen])
            if hdr[0] == 0 and hdr[1] == 0:
                break                       #no more pointers will follow
            '''
            0x01 0x00 0x00 0x00 0x00
                This record relates to a B-tree root page which obviously does not have a parent page, hence the page number being indicated as zero.
            0x02 0x00 0x00 0x00 0x00
                This record relates to a free page, which also does not have a parent page.
            0x03 0xVV 0xVV 0xVV 0xVV (where VV indicates a variable)
                This record relates to the first page in an overflow chain. The parent page number is the number of the B-Tree page containing the B-Tree cell to which the overflow chain belongs.
            0x04 0xVV 0xVV 0xVV 0xVV (where VV indicates a variable)
                This record relates to a page that is part of an overflow chain, but not the first page in that chain. The parent page number is the number of the previous page in the overflow chain linked-list.
            0x05 0xVV 0xVV 0xVV 0xVV (where VV indicates a variable)
                This record relates to a page that is part of a table or index B-Tree structure, and is not an overflow page or root page. The parent page number is the number of the page containing the parent tree node in the B-Tree structure.
            '''
            counter += 1
            ptrmapdict = dict(zip(self._ptrmaphdrkeys,list(hdr)))
            self.ptrMap.append(ptrmapdict)
            offset += ptrMapLen

    def _readDBFile(self):
        try:
            f=open(self.opt['sqlitedb'],"rb")
            self.data = f.read()
        except:
            print ("File not Found")
            self.data = None

    def _parsePageHeader(self, page, pageNr):
        pageDict = dict ()
        if pageNr == 1:
            pageHeader = unpack(self._lbtreefrmt, page[100:108])
        else:
            pageHeader = unpack(self._lbtreefrmt, page[:8])
        pageByte, fbOffset, cellQty, cellOffset, freebytes = pageHeader

        if pageByte == INTERIOR_TABLE_BTREE_PAGE:
           if pageNr == 1:
               rmpointer = unpack(self._ibtreefrmt, page[108:112])[0]
           else:
               rmpointer = unpack(self._ibtreefrmt, page[8:12])[0]
        else:
            rmpointer = None

        pageHeader = list(pageHeader)
        pageHeader.append(rmpointer)
        pageDict = dict(zip(self._btreehdrkeys, pageHeader))
        return pageDict

    def _parseDBHeader(self):
        self.dbHeaderDict = dict(zip(self._dbhdrkeys,list(self._unpackDBHeader())))

    def _parseDBSchema(self, pageNum):
        # based on https://github.com/n0fate/walitean
        TABLE = b'table'
        CREATETABLE = b'CREATE TABLE'
        buf = b''
        dbschema = {}
        columnsdic = {}
        tables = []
        dbtable = {}
        page = self.dbPages[int(pageNum)]
        tables = page["celldata"]
        if self.hasLeafPages(page) == True:
            for leafpage in page["leafpages"]:
                if leafpage < self.dbHeaderDict["in_header_database_size"]:
                    if self.hasCelldata(self.dbPages[leafpage]):
                        tables += self.dbPages[leafpage]["celldata"]

        for table in tables:
            columnlst = []
            dbtable = {}
            strcolumns = None
            if not table[0] in sql_type:
                continue
            dbtable['type'] = table[0]
            dbtable['name'] = table[1]
            dbtable['rootpage'] = table[3]


            if dbtable['type'] == 'table':
                strcolumns = self._findSQLCmd(table[4])
                if strcolumns == "ERROR":
                    continue
                l = strcolumns.find('UNIQUE (')
                r = strcolumns.find(')')
                if l > 0 and r > l:
                    strcolumns = strcolumns[:l-1] + strcolumns[r+1:]

#                if strcolumns[0] == ' ':    # remove byte if first byte is space
#                    strcolumns = strcolumns[1:]
                strcolumns = strcolumns.lstrip(' ')
                strcolumns = strcolumns.rstrip(' ')
                strcolumns = strcolumns.replace(' REFERENCES','')
                for column in strcolumns.split(','):
                    column = column.lstrip(' ')
                    column = column.replace('"','')
                    if column == '':
                        continue
                    if column[0] == ' ':
                        column = column[1:]
                    if str(column).startswith('PRIMARY') or str(column).startswith('UNIQUE'):
                        continue
                    try:
                        column.index('UNIQUE (')
                        continue
                    except ValueError:
                        pass
                    columninfo = []
                    columnname = ""
                    columntype = ""
                    if len(column.split(' ')) >= 2:
                        columnname = column.split(' ')[0]
                        columntype = column.split(' ')[1]
                        columninfo.append(columnname)
                        columninfo.append(columntype)
                    if columninfo.__len__() != 0:
                        columnlst.append(columninfo)

                if len(columnlst):
                    dbtable['schema'] = columnlst
                else:
                    dbtable['schema'] = []

            columnsdic[dbtable['name']] = dbtable
        return columnsdic

    def _unpackDBHeader(self):
        try:
            dbheader = unpack(self._dbhdrfrmt, self.data[:100])
        except:
            dbheader = "No valid SQLite database"
        return dbheader

    def _remove_ascii_non_printable(self, chunk):
        chunk = ' '.join(chunk .split())
        return ''.join([ch for ch in chunk if ord(ch) > 31 and ord(ch) < 126 or ord(ch) ==9])

    def _remove_non_printable(self, chunk):
        ret = ""
        for ch in chunk:
            if ch > 31 and ch < 126 or ch == 9:
                ret = ret + chr(ch)
        return ret.strip()

    def _makeTmpDir(self):
        try:
            tmpdir = tempfile.mkdtemp()
        except:
            tmpdir = ""
        return tmpdir

    def _writeBinary (self,name, data):

        try:
            ext = self._filetype(data[0:12])
            destname = self.tmpdir + "/" + str(name) + "." + ext
            with open(destname, 'wb') as output_file:
                output_file.write(data)
            output_file.close()
        except:
            destname = ""

        return destname

    def _filetype(self, header):
        if ((header[:4] == JPGHEADER) and (header[6:] != JPGIDENT)) or ((header[:4] == EXIFHEADER) and (header[6:] != EXIFIDENT)):
            return 'jpg'
        elif (header[0:MA4HEADERLEN] == MA4HEADER):
            return 'ma4'
        elif (header[0:MOVHEADERLEN] == MOVHEADER):
            return 'mov'
        elif (header[0:BPLISTHEADERLEN] == BPLISTHEADER):
            return 'bplist'
        elif (header[0:MP3HEADERLEN] == MP3HEADER):
            return 'mp3'
        else:
            return 'bin'

    def printDBheader(self):

        if self.dbHeaderDict["pageSize"] == 1:
            print("Page size in bytes:".ljust(35,' ') + "65536")
        else:
            print("Page size in bytes:".ljust(35,' ') + "%8s" %str(self.dbHeaderDict["pageSize"]))
        print("write_version:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["write_version"]))
        print("read_version:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["read_version"]))
        print("unused_reservered_space:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["unused_reserved_space"]))
        print("maximum_embedded_payload_fraction:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["maximum_embedded_payload_fraction"]))
        print("minimum_embedded_payload_fraction:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["minimum_embedded_payload_fraction"]))
        print("leaf_payload_fraction:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["leaf_payload_fraction"]))
        print("file_change_counter:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["file_change_counter"]))
        print("in_header_database_size:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["in_header_database_size"]))
        print("first_freelist_trunk_page:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["first_freelist_trunk_page"]))
        print("total_num_freelist_pages:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["total_num_freelist_pages"]))
        print("schema_cookie:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["schema_cookie"]))
        if self.dbHeaderDict["schema_format_number"] == 1:
            sf = "SQLite v3.0.0"
        elif self.dbHeaderDict["schema_format_number"] == 2:
            sf = "SQLite v3.1.3 (2005)"
        elif self.dbHeaderDict["schema_format_number"] == 3:
            sf = "SQLite v3.1.4 (2005)"
        elif self.dbHeaderDict["schema_format_number"] == 4:
            sf = "SQLite v3.3.0 (2006) or higher"
        else:
            sf = "Invalid Schema Format!"

        print("schema_format_number:".ljust(35, ' ') + "%8s (%s)" %(str(self.dbHeaderDict["schema_format_number"]),sf))
        print("default_page_cache_size:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["default_page_cache_size"]))
        print("largest_root_b_tree:".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["largest_root_b_tree"]))

        if self.dbHeaderDict["database_text_encoding"] == 1:
            te = "UTF-8"
        elif self.dbHeaderDict["database_text_encoding"] == 2:
            te = "UTF-16le"
        elif self.dbHeaderDict["database_text_encoding"] == 3:
            te = "UTF-16be"
        else:
            te = "Invalid Text Encoding!"
        print("database_text_encoding:".ljust(35, ' ') + "%8s (%s)" %(str(self.dbHeaderDict["database_text_encoding"]),te))
        print("user_version".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["user_version"]))
        print("incremental_vacuum".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["incremental_vacuum"]))
        print("application_id".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["application_id"]))
        #print("reserved".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["reserved"]))
        print("version_valid_for_number".ljust(35, ' ') + "%8s" %str(self.dbHeaderDict["version_valid_for_number"]))

        print("sqlite_version_number:".ljust(35, ' ') + "%8s (%s)" %(str(self.dbHeaderDict["sqlite_version_number"]),str(self.dbHeaderDict["sqlite_version_number"]).replace("00","0").replace("0",".")))

        if self.opt['debug']:
            print('\n##################################################################################\n')
            #print("%4i %10s %45s %8s %23s %5s" %(i,str(pageNr), str(tbl_name), str(tbl_type), str(pageType), str(col_count)))
            for page in self.dbPages:
                print("Page Nr: %3s\tPage offset: %8s\tPage Type: %20s" %(str(self.dbPages[page]['pageNr']), str(self.dbPages[page]['pageOffset']), str(self.dbPages[page]['pageType'])))
                if self.dbPages[page]['isRootPage'] == True:
                    print("Is Root Page: %5s" %(self.dbPages[page]['isRootPage']))
                if page == 1:
                    phOffset = 100
                else:
                    phOffset = 0
                if self.dbPages[page]["pageHeader"]["pageByte"] == INTERIOR_TABLE_BTREE_PAGE:
                    phlen = 12
                else:
                    phlen = 8

                print("Page header\tOffset: %8s (%s)\tLen: %4s" %(str(self.dbPages[page]['pageOffset']),str(phOffset), str(phlen)))

                print("\t{0:25s} {1:>5s}".format("Flag:", str(self.dbPages[page]["pageHeader"]["pageByte"])))
                print("\t{0:25s} {1:>5s}".format("First free block:", str(self.dbPages[page]["pageHeader"]["fbOffset"])))
                print("\t{0:25s} {1:>5s}".format("No of cells:", str(self.dbPages[page]["pageHeader"]["cellQty"])))
                print("\t{0:25s} {1:>5s}".format("First byte of content:", str(self.dbPages[page]["pageHeader"]["cellOffset"])))
                print("\t{0:25s} {1:>5s}".format("Fragmented byte count:", str(self.dbPages[page]["pageHeader"]["freebytes"])))
                if self.dbPages[page]["pageHeader"]["rmpointer"] == None:
                    rmp = ""
                else:
                    rmp = self.dbPages[page]["pageHeader"]["rmpointer"]
                print("\t{0:25s} {1:>5s}".format("Right most pointer:", str(rmp)))


                if self.dbPages[page]["pageHeader"]["cellQty"] > 0 and self.dbPages[page]['pageType'] != "Overflow Page":
                    print("\n\t{0:23s} {1:>5s}".format("Cell pointer array:", "")) #str(self.dbPages[page]["pageHeader"]["cellQty"])))

                    for cp in range(0,(self.dbPages[page]["pageHeader"]["cellQty"]*2),2):
                        start = cp
                        end = cp + 2
                        cellp = unpack('>H', self.dbPages[page]["cellPointer"][start:end])[0]
                        cellstart = self.dbPages[page]['pageOffset'] + cellp
                        print("\t\t{0:23s} {1:>5s}".format("Cell pointer:", str(cellp)))

                        if (self.dbPages[page]["pageHeader"]["pageByte"] == LEAF_TABLE_BTREE_PAGE):
                            cellheader, payloadheaderlen, dataoffset, payloadlen, recordnum, payloadsizeincell, overflowpageoffset,overflowpagenum = self._parseLeafTableCellHeader(self.data, cellstart, freespace=False)
                            print("\t\t\t{0:15s} {1:>5s}".format("Payload length:", str(payloadlen)))
                            print("\t\t\t{0:15s} {1:>5s}".format("Row ID:", str(recordnum)))
                            print("\t\t\tPayload")
                            print("\t\t\t\t{0:22s} {1:>8s}".format("Payload header len:", str(payloadheaderlen)))
                            print("\t\t\t\t{0:22s} {1:>8s}".format("Data offset:", str(dataoffset)))
                            print("\t\t\t\t{0:22s} {1:>8s}".format("Overflow page offset:", str(overflowpageoffset)))
                            print("\t\t\t\t{0:22s} {1:>8s}".format("Overflow page num:", str(overflowpagenum)))
                        elif (self.dbPages[page]["pageHeader"]["pageByte"] == LEAF_INDEX_BTREE_PAGE):
                            cellheader,payloadheaderlen,dataoffset,payloadlen,overflowpageoffset,overflowpagenum = self._parseLeafIndexCellHeader(self.data, self.dbPages[page]['pageOffset'])
                            print("\t\t\t{0:15s} {1:>5s}".format("Payload length:", str(payloadlen)))
                            print("\t\t\tPayload")
                            print("\t\t\t\t{0:22s} {1:>8s}".format("Payload header len:", str(payloadheaderlen)))
                            print("\t\t\t\t{0:22s} {1:>8s}".format("Data offset:", str(dataoffset)))
                            print("\t\t\t\t{0:22s} {1:>8s}".format("Overflow page offset:", str(overflowpageoffset)))
                            print("\t\t\t\t{0:22s} {1:>8s}".format("Overflow page num:", str(overflowpagenum)))
                        elif (self.dbPages[page]["pageHeader"]["pageByte"] == INTERIOR_TABLE_BTREE_PAGE):
                            cellheader, dataoffset, pagechildnum, recordnum = self._parseInteriorTableCellHeader(self.data,cellstart)
                            print("\t\t\t{0:15s} {1:>8s}".format("Left child:", str(pagechildnum)))
                            print("\t\t\t{0:15s} {1:>8s}".format("Row ID:", str(recordnum)))




                if self.hasLeafPages(self.dbPages[page]) == True:
                    print("Leaf pages: %s" %(self.dbPages[page]['leafpages']))

                if self.hasDeleted(self.dbPages[page]) == True:
                    print("Deleted pages: %s" %(self.dbPages[page]['deletedpages']))
                print('\n++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n')

    def printPtrMap(self):

        if self.ptrMap.__len__() > 0:
            print("Database has a pointer map...")
            pos = 0
            for ptrmap in self.ptrMap:
                idx = ptrmap['pageNr']
                rp = ptrmap['pageType']
                print("idx: %s\tpage: %s\troot page: %s" %(str(pos),str(pos+3),str(rp)))
                pos += 1

    def printDBSchema(self):
        print("Parsed database schema...")
        i=0
        for dbtable in self.dbSchema:
            i+=1
            print("(%i) Table: %s" %(i,str(dbtable)))
            print("\tTable name: %s" %str(self.dbSchema[dbtable]['name']))
            print("\tRoot page: %s" %str(self.dbSchema[dbtable]['rootpage']))
            if self.dbSchema[dbtable]['type']== 'table':
                print("\tSchema:")
                for key, value in self.dbSchema[dbtable]['schema']:
                    print("\t\t %s:\t%s" %(str(key),str(value)))

    def printDBData(self):

        for ipage in self.dbPages:
            if ipage == 1 or self.dbPages[ipage]['pageType'] == "Overflow Page":
                continue

            self.printTable(number=ipage)

    def printTable(self, name=None, number=None):
        page = None
        schema = {}
        tblname = "???"
        colheader = "???"

        if name == None and number == None:
            return
        if name is not None:
            number = self._lookUpTable(name)
        if number is not None:
            try:
                page = self.dbPages[int(number)]
            except:
                page = None

        if page is None:
            return
        if self.isRootPage(page) == True:
            try:
                tblname, colheader = page["schema"].popitem()
                schema = self.dbSchema[tblname]['schema']
            except:
                tblname = "???"
                colheader = "???"
            print("PageNr: %s\tTable name: %s" %(str(page["pageNr"]),str(tblname)))
            hdr = "Page;Type;"
            hdr += ";".join(map(str,colheader))
            print(hdr)

        #if the page has leafpages, the page cells contain only the pointer to the leafpages
        if self.hasCelldata(page) == True:
            rownum = 0
            for row in page["celldata"]:
                rownum += 1
                rowdata = str(page["pageNr"]) + ";C"
                i=0
                for cell in row:
                    fname = ''
                    try:
                        if (schema[i][1] == "BLOB"):
                            if (self.opt['bin2out']):
                                rowdata += ";'" + str(cell) + "'"
                            else:
                                rowdata += ";"
                            if (self.opt['bin2file']):
                                fname = self._writeBinary(tblname+"_"+str(page["pageNr"])+"_"+str(rownum)+"_"+str(i), cell)
                                if (fname != "") and not self.opt['bin2out']:
                                    rowdata += "'" + fname + "'"
                        else:
                            rowdata += ";'" + str(cell) + "'"
                    except:
                        rowdata += ";'" + str(cell) + "'"
                    i+=1
#                rowdata += "'"
                print(rowdata)
        if self.opt['freespace']:
            for freespace in page["freespace"]:
                if self.opt['debug'] == True:
                    if self.opt['verbose'] == True:
                        print(str(page["pageNr"]) + ";F;'';" + "'" + freespace + "'")
                    else:
                        print(str(page["pageNr"]) + ";F;'';" + "'" + self._remove_non_printable(freespace) + "'")

                for element in page["fs_celldata"]:
                    rownum += 1
                    rowdata = str(page["pageNr"]) + ";FC"
                    i=0
                    for cell in row:
                        rowdata += ";"
                        try:
                            if (schema[i][1] == "BLOB"):
                                if (self.opt['bin2out']):
                                    rowdata += "'" + str(cell) + "'"
                                #else:
                                #    rowdata += ";"
                                if (self.opt['bin2file']):
                                    fname = self._writeBinary(tblname+"_"+str(page["pageNr"])+"_"+str(rownum)+"_"+str(i), cell)
                                    if (fname != "") and not self.opt['bin2out']:
                                        rowdata += "'" + fname + "'"
                            else:
                                rowdata += "'" + str(cell) + "'"
                        except:
                            rowdata += "'" + str(cell) + "'"
                        i+=1
                    print(rowdata)


        if self.opt['unallocated']:
            if self.opt['verbose'] == True:
                print(str(page["pageNr"]) + ";U;'';" + "'" + page["unallocated"] + "'")
            else:
                data = self._remove_non_printable(page["unallocated"])
                if data != "":
                    print(str(page["pageNr"]) + ";U;'';" + "'" + data + "'")

        if self.hasLeafPages(page) == True:
            for leafpage in page["leafpages"]:
                if self.hasCelldata(self.dbPages[leafpage]) == True:
                    rownum = 0
                    for row in self.dbPages[leafpage]["celldata"]:
                        rownum += 1
                        rowdata = str(leafpage) + ";C"
                        i=0
                        for cell in row:
                            rowdata += ";"
                            try:
                                if (schema[i][1] == "BLOB"):
                                    if (self.opt['bin2out']):
                                        rowdata += "'" + str(cell) + "'"
                                    #else:
                                    #    rowdata += ";"
                                    if (self.opt['bin2file']):
                                        fname = self._writeBinary(tblname+"_"+str(leafpage)+"_"+str(rownum)+"_"+str(i), cell)
                                        if (fname != "") and not self.opt['bin2out']:
                                            rowdata += "'" + fname + "'"
                                else:
                                    rowdata += "'" + str(cell) + "'"
                            except:
                                rowdata += "'" + str(cell) + "'"
                            i+=1
                        print(rowdata)
                if self.opt['freespace'] and self.hasFreespace(self.dbPages[leafpage]) == True:
                    rownum = 0

                    for freespace in self.dbPages[leafpage]["freespace"]:
                        if self.opt['debug'] == True:
                            if self.opt['verbose'] == True:
                                print(str(leafpage) + ";F;'';" + "'" + str(freespace) + "'")
                            else:
                                print(str(leafpage) + ";F;'';" + "'" + self._remove_non_printable(freespace) + "'")

                        for element in self.dbPages[leafpage]["fs_celldata"]:
                            rownum += 1
                            rowdata = str(leafpage) + ";FC"
                            i=0
                            for cell in element:
                                rowdata += ";"
                                try:
                                    if (schema[i][1] == "BLOB"):
                                        if (self.opt['bin2out']):
                                            rowdata += "'" + str(cell) + "'"
                                        #else:
                                        #    rowdata += ";"
                                        if (self.opt['bin2file']):
                                            fname = self._writeBinary(tblname+"_"+str(leafpage)+"_"+str(rownum)+"_"+str(i), cell)
                                            if (fname != "") and not self.opt['bin2out']:
                                                rowdata += "'" + fname + "'"
                                    else:
                                        rowdata += "'" + str(cell) + "'"
                                except:
                                    rowdata += "'" + str(cell) + "'"
                                i+=1
                            print(rowdata)

                if self.opt['unallocated'] and self.hasUnallocated(self.dbPages[leafpage]) == True:
                    if self.opt['verbose'] == True:
                        print(str(leafpage) + ";U;'';" + "'" + self.dbPages[leafpage]["unallocated"] + "'")
                    else:
                        data = self._remove_non_printable(self.dbPages[leafpage]["unallocated"])
                        if data != "":
                            print(str(leafpage) + ";U;'';" + "'" + data + "'")

        if self.opt['deleted'] and self.hasDeleted(page) == True:
            for deletedpage in page["deletedpages"]:
                if self.hasCelldata(self.dbPages[deletedpage]) == True:
                    rownum = 0
                    for row in self.dbPages[deletedpage]["celldata"]:
                        rownum += 1
                        rowdata = str(deletedpage) + ";DC"
                        i=0
                        for cell in row:
                            rowdata += ";"
                            try:
                                if (schema[i][1] == "BLOB"):
                                    if (self.opt['bin2out']):
                                        rowdata += "'" + str(cell) + "'"
                                    #else:
                                    #    rowdata += ";"
                                    if (self.opt['bin2file']):
                                        fname = self._writeBinary(tblname+"_"+str(deletedpage)+"_"+str(rownum)+"_"+str(i), cell)
                                        if (fname != "") and not self.opt['bin2out']:
                                            rowdata += "'" + fname + "'"
                                else:
                                    rowdata += "'" + str(cell) + "'"
                            except:
                                rowdata += "'" + str(cell) + "'"
                            i+=1
                        print(rowdata)

                if self.opt['freespace'] and self.hasFreespace(self.dbPages[deletedpage]) == True:

                    for freespace in self.dbPages[deletedpage]["freespace"]:
                        if self.opt['debug'] == True:


                            if self.opt['verbose'] == True:
                                print(str(deletedpage) + ";DF;'';" + "'" + freespace + "'")
                            else:
                                print(str(deletedpage) + ";DF;'';" + "'" + self._remove_non_printable(freespace) + "'")

                        for element in self.dbPages[deletedpage]["fs_celldata"]:
                            rownum += 1
                            rowdata = str(deletedpage) + ";DFC"
                            i=0
                            for cell in element:
                                rowdata += ";"
                                try:
                                    if (schema[i][1] == "BLOB"):
                                        if (self.opt['bin2out']):
                                            rowdata += "'" + str(cell) + "'"
                                        #else:
                                        #    rowdata += ";"
                                        if (self.opt['bin2file']):
                                            fname = self._writeBinary(tblname+"_"+str(deletedpage)+"_"+str(rownum)+"_"+str(i), cell)
                                            if (fname != "") and not self.opt['bin2out']:
                                                rowdata += "'" + fname + "'"
                                    else:
                                        rowdata += "'" + str(cell) + "'"
                                except:
                                    rowdata += "'" + str(cell) + "'"
                                i+=1
                            print(rowdata)


                if self.opt['unallocated'] and self.hasUnallocated(self.dbPages[deletedpage]) == True:
                    if self.opt['verbose'] == True:
                        print(str(deletedpage) + ";DU;'';" + "'" + self.dbPages[deletedpage]["unallocated"] + "'")
                    else:
                        data = self._remove_non_printable(self.dbPages[deletedpage]["unallocated"])
                        if data != "":
                            print(str(deletedpage) + ";DU;'';" + "'" + data + "'")

    def _lookUpTable(self, tbl_name):

        for table in self.dbSchema:
            if self.dbSchema[table]["name"] == tbl_name:
                return self.dbSchema[table]["rootpage"]
        return None

    def listAllTables(self):

        i=0
        print("Nr".center(6) + "Page Num".center(10) + "Table Name".center(46) + "Table Type".center(10) + "Page Type".center(25) + "Cols".center(6))
        for dbtable in sorted(self.dbSchema, key=lambda table: table[2]):
            i+=1
            tbl_name = self.dbSchema[dbtable]['name']
            tbl_type = self.dbSchema[dbtable]['type']
            if tbl_type == "table":
                tbl_type = "TABLE"
            pageNr = self.dbSchema[dbtable]['rootpage']
            if pageNr == "-" or pageNr is None or pageNr == '0':
                pageNr = ""
                pageType = ""
            else:
                pageType = self.dbPages[pageNr]['pageType']
            col_count = 0
            try:
                col_count = self.dbSchema[dbtable]['schema'].__len__()
            except:
                pass

            print("%4i %10s %45s %8s %23s %5s" %(i,str(pageNr), str(tbl_name), str(tbl_type), str(pageType), str(col_count)))

    def printDBMap(self):
        pass

    '''
    Funtions borrowed from SQLiteZer
    https://github.com/NotionalLabs/SQLiteZer

    Copyright [2013] [Jim Hung]

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.

    '''
    def _getVarInt(self,bytestring):
        """
        As with _getVarIntOfs, but with an already-known length byte string.
        Example: result = _getVarInt(file.read(3))
        Warning: This methid will attempt to decode the bytestring regardless
        of whether it's a valid VarInt.
        Pass byte string to decode.
        Returns VarInt value.
        """
        varintlen = len(bytestring)
        varintval = bytestringpos = 0

        for i in reversed(range(0,varintlen)):
            if (i == 0):
                byteval = ord(bytestring[bytestringpos])
                varintval+=byteval
            else:
                byteval = ord(bytestring[bytestringpos])
                varintval+=(byteval - 128)*(2**(i*7))
            bytestringpos+=1

        return varintval,varintlen

    def _getVarIntOfs(self, data, offset):
        """
        Decode Huffman-coded two's compliment integers used for storing 64-bit
        variable-length integers. Implements Mike Harrington's example technique
        for decoding SQLite VarInts (https://mobileforensics.wordpress.com/2011/
        09/17/huffman-coding-in-sqlite-a-primer-for-mobile-forensics/). SQLite
        spec allows for between 1-9 byte runs per VarInt - this method should
        scale to that size, despite such huge values being rare in practice.

        Pass starting byte offset to decode.
        Returns tuple(VarInt value and the VarInt length).
        """

        varintlen = varintval = 0
        of = offset
        while True:
            if((ord(data[offset:offset+1])&(1<<7))!=0):
                varintlen+=1
                offset+=1
            else:
                varintlen+=1
                break
        offset = int(of)
        for i in reversed(range(0,varintlen)):
            if (i == 0):
                byteval = ord(data[offset:offset+1])
                varintval+=byteval
            else:
                byteval = ord(data[offset:offset+1])
                offset +=1
                varintval+=(byteval - 128)*(2**(i*7))

        return varintval,varintlen

    def _getoverflowdata(self, pageNr):

        overlfowdata = b''
        pagenum = int(pageNr)-1
        while pagenum > 0 and pagenum < self.dbHeaderDict['in_header_database_size']:
            self.overflowpages.append(pagenum+1)
            offset = pagenum * self.dbHeaderDict['pageSize']
            next_pagenum = unpack('>I', self.data[offset:offset+4])[0] - 1
            start = offset + 4
            end = offset + self.dbHeaderDict['pageSize'] - self.dbHeaderDict['unused_reserved_space']
            overlfowdata += self.data[start:end]
            pagenum = int(next_pagenum)
        return overlfowdata

    def _parseCell(self, data, offset, cellformat):
        """
        Parse a B-Tree Leaf Page Cell, given it's starting absolute byte offset.
        Pass absolute starting byte offset for the cell header.
        Returns the parsed cell as a list in the form:

        """
        celldatalist = list()
        cellheader = None
        dataoffset = 0
        payloadlen = 0
        recordnum = None
        overflowpageoffset = 0
        overflowpagenum = 0
        payloadsizeincell = 0
        payloadheaderlen = 0
        payload = b''

        if (cellformat == LEAF_TABLE_BTREE_PAGE):
            cellheader, payloadheaderlen, dataoffset, payloadlen, recordnum, payloadsizeincell, overflowpageoffset,overflowpagenum = self._parseLeafTableCellHeader(data, offset, freespace=False)
            #end = int(round(self._getPayloadSizeInCell(payloadlen)))
            payload = data[dataoffset:dataoffset + payloadsizeincell]
            if (overflowpagenum > 0) and (overflowpagenum is not None):
                payload += self._getoverflowdata(overflowpagenum)
            data = payload
            dataoffset = 0
            for field in cellheader:
                dataoffset = int(dataoffset)
                if field[0] == "NULL":
                    celldatalist.append(recordnum)
                elif field[0] == "ST_INT8":
                    celldatalist.append(ord(unpack(">c",data[dataoffset:dataoffset+1])[0]))
                    dataoffset+=field[1]
                elif field[0] == "ST_INT16":
                    celldatalist.append(unpack(">h",data[dataoffset:dataoffset+2])[0])
                    dataoffset+=field[1]
                elif field[0] == "ST_INT24":
                    celldatalist.append("-")
                    dataoffset+=field[1]
                elif field[0] == "ST_INT32":
                    celldatalist.append(unpack(">i",data[dataoffset:dataoffset+4])[0])
                    dataoffset+=field[1]
                elif field[0] == "ST_INT48":
                    celldatalist.append(self._unpack48(data[dataoffset:dataoffset + 6]))
                    dataoffset+=field[1]
                    #celldatalist.append("ST_INT48 - NOT IMPLEMENTED!") # NOT IMPLEMENTED YET!
                    #dataoffset+=field[1]
                elif field[0] == "ST_INT64":
                    celldatalist.append(unpack(">q",data[dataoffset:dataoffset+8])[0])
                    dataoffset+=8
                elif field[0] == "ST_FLOAT":
                    celldatalist.append(unpack(">d",data[dataoffset:dataoffset+8])[0])
                    dataoffset+=8
                elif field[0] == "ST_C0":
                    celldatalist.append("0")
                elif field[0] == "ST_C1":
                    celldatalist.append("1")
                elif field[0] == "ST_BLOB":
                    cell = data[dataoffset:dataoffset+int(field[1])]
                    celldatalist.append(cell)
                    dataoffset+=field[1]
                elif field[0] == "ST_TEXT":
                    try:
                        celldatalist.append(data[dataoffset:dataoffset+int(field[1])].decode('UTF-8'))
                    except:
                        try:
                            celldatalist.append(str(data[dataoffset:dataoffset+int(field[1])]))
                        except:
                            pass

                    dataoffset+=field[1]
                else:
                    pass
                    #print(field[0])
        elif (cellformat == LEAF_INDEX_BTREE_PAGE):
            cellheader,payloadheaderlen,dataoffset,payloadlen,overflowpageoffset,overflowpagenum = self._parseLeafIndexCellHeader(data, offset)
            for field in cellheader:
                dataoffset = int(dataoffset)
                if field[0] == "NULL":
                    celldatalist.append("-")
                elif field[0] == "ST_INT8":
                    celldatalist.append(ord(unpack(">c",data[dataoffset:dataoffset+1])[0]))
                    dataoffset+=field[1]
                elif field[0] == "ST_INT16":
                    celldatalist.append(unpack(">h",data[dataoffset:dataoffset+2])[0])
                    dataoffset+=field[1]
                elif field[0] == "ST_INT24":
                    celldatalist.append("-")
                    dataoffset+=field[1]
                elif field[0] == "ST_INT32":
                    celldatalist.append(unpack(">i",data[dataoffset:dataoffset+4])[0])
                    dataoffset+=field[1]
                elif field[0] == "ST_INT48":
                    celldatalist.append(self._unpack48(data[dataoffset:dataoffset + 6]))
                    dataoffset+=field[1]
                    #celldatalist.append("ST_INT48 - NOT IMPLEMENTED!") # NOT IMPLEMENTED YET!
                    #dataoffset+=field[1]
                elif field[0] == "ST_INT64":
                    celldatalist.append(unpack(">q",data[dataoffset:dataoffset+8])[0])
                    dataoffset+=8
                elif field[0] == "ST_FLOAT":
                    celldatalist.append(unpack(">d",data[dataoffset:dataoffset+8])[0])
                    dataoffset+=8
                elif field[0] == "ST_C0":
                    celldatalist.append("-")
                elif field[0] == "ST_C1":
                    celldatalist.append("-")
                elif field[0] == "ST_BLOB":
                    celldatalist.append(data[dataoffset:dataoffset+int(field[1])])
                    dataoffset+=field[1]
                elif field[0] == "ST_TEXT":
                    try:
                        celldatalist.append(data[dataoffset:dataoffset+int(field[1])].decode('UTF-8'))
                    except:
                        try:
                            celldatalist.append(str(data[dataoffset:dataoffset+int(field[1])]))
                        except:
                            pass

                    dataoffset+=field[1]
                else:
                    pass
                    #print(field[0])
        elif (cellformat == INTERIOR_TABLE_BTREE_PAGE):
            cellheader, dataoffset, pagechildnum, recordnum = self._parseInteriorTableCellHeader(data, offset)
            celldatalist.append(pagechildnum)
            celldatalist.append(recordnum)
        elif (cellformat == INTERIOR_INDEX_BTREE_PAGE):
            cellheader,payloadheaderlen, dataoffset,payloadlen,overflowpageoffset,overflowpagenum = self._parseLeafIndexCellHeader(data, offset)
            '''
            for field in cellheader:
                dataoffset = int(dataoffset)
                if field[0] == "NULL":
                    celldatalist.append("-")
                elif field[0] == "ST_INT8":
                    celldatalist.append(ord(unpack(">c",data[dataoffset:dataoffset+1])[0]))
                    dataoffset+=field[1]
                elif field[0] == "ST_INT16":
                    celldatalist.append(unpack(">h",data[dataoffset:dataoffset+2])[0])
                    dataoffset+=field[1]
                elif field[0] == "ST_INT24":
                    celldatalist.append("-")
                    dataoffset+=field[1]
                elif field[0] == "ST_INT32":
                    celldatalist.append(unpack(">i",data[dataoffset:dataoffset+4])[0])
                    dataoffset+=field[1]
                elif field[0] == "ST_INT48":
                    celldatalist.append(self.unpack48(data[dataoffset:dataoffset+6]))
                    dataoffset+=field[1]
                elif field[0] == "ST_INT64":
                    celldatalist.append(unpack(">q",data[dataoffset:dataoffset+8])[0])
                    dataoffset+=8
                elif field[0] == "ST_FLOAT":
                    celldatalist.append(unpack(">d",data[dataoffset:dataoffset+8])[0])
                    dataoffset+=8
                elif field[0] == "ST_C0":
                    celldatalist.append("-")
                elif field[0] == "ST_C1":
                    celldatalist.append("-")
                elif field[0] == "ST_BLOB":
                    celldatalist.append(data[dataoffset:dataoffset+int(field[1])])
                    dataoffset+=field[1]
                elif field[0] == "ST_TEXT":
                    try:
                        celldatalist.append(data[dataoffset:dataoffset+int(field[1])].decode('UTF-8'))
                    except:
                        try:
                            celldatalist.append(str(data[dataoffset:dataoffset+int(field[1])]))
                        except:
                            pass

                    dataoffset+=field[1]
                else:
                    print(field[0])
                '''
        else:
            pass

        return celldatalist, payloadlen

    def _getPayloadSizeInCell(self, payloadWholeSize):
        """
        @note
        See: README.org - Track overflow pages

        @return
        Local payload size for this cell.
        """
        payloadSize = payloadWholeSize
        usableSize = self.dbHeaderDict["pageSize"]
        maxLocal = usableSize - 35
        #not really sure if int or round
        minLocal = int(((usableSize - 12) * 32 / 255)) - 23
        if payloadSize <= maxLocal:
            return payloadSize
        localSize = minLocal + ((payloadSize - minLocal) % (usableSize - 4))
        sizeInThisPage = minLocal if localSize > maxLocal else localSize
        return sizeInThisPage

    def _parseLeafTableCellHeader(self, data, offset, freespace=None):
        """
        Parse a B-Tree Leaf Page Cell Header, given it's starting absolute byte
        offset.
        Pass absolute starting byte offset for the cell header to be decoded.
        Returns tuple containing a list of tuples in the form
        [(String type,int length),...], and the starting offset of the payload
        fields.
        """

        headerlist = list()
        overflowpagenum = 0
        payloadsizeincell = 0
        overflowpageoffset = offset
        recordnum = 0
        payloadlen = 0
        length = 0
        if freespace is False:
            # Payload length
            payloadlen,length = self._getVarIntOfs(data, offset)
            offset+=length
            overflowpageoffset+=length
            # Record Number
            recordnum,length = self._getVarIntOfs(data, offset)
            offset+=length
            overflowpageoffset+=length

        # Payload Header Length
        payloadheaderlen,length = self._getVarIntOfs(data, offset)
        payloadheaderlenofs = offset + payloadheaderlen
        offset+=length

        # Overflow Page Number
        if freespace is False:
            payloadsizeincell = int(round(self._getPayloadSizeInCell(payloadlen)))
            overflowpageoffset += payloadsizeincell
            overflowpageoffset = int(overflowpageoffset)
            if (payloadlen > (self.dbHeaderDict["pageSize"] - self.dbHeaderDict["unused_reserved_space"] - 35)):
                overflowpagenum = unpack(">I",data[overflowpageoffset:overflowpageoffset+4])[0]

            if (overflowpagenum <= 1) or (overflowpagenum >= self.dbHeaderDict['in_header_database_size']):
                overflowpagenum = 0

        # Payload Fields
        while offset < (payloadheaderlenofs):
            fieldtype,length = self._getVarIntOfs(data, offset)
            # Determine Serial Type
            if fieldtype == 0:
                headerlist.append(("NULL",0))
            elif fieldtype == 1:
                headerlist.append(("ST_INT8",1))
            elif fieldtype == 2:
                headerlist.append(("ST_INT16",2))
            elif fieldtype == 3:
                headerlist.append(("ST_INT24",3))
            elif fieldtype == 4:
                headerlist.append(("ST_INT32",4))
            elif fieldtype == 5:
                headerlist.append(("ST_INT48",6))
            elif fieldtype == 6:
                headerlist.append(("ST_INT64",8))
            elif fieldtype == 7:
                headerlist.append(("ST_FLOAT",8))
            elif fieldtype == 8:
                headerlist.append(("ST_C0",0))
            elif fieldtype == 9:
                headerlist.append(("ST_C1",0))
            elif fieldtype > 11:
                if (fieldtype%2) == 0:
                    headerlist.append(("ST_BLOB",(fieldtype-12)/2))
                else:
                    headerlist.append(("ST_TEXT",(fieldtype-13)/2))
            else:
                headerlist.append(("Reserved: %s" % str(fieldtype),0))
            offset+=length

        return headerlist, payloadheaderlen, offset, payloadlen, recordnum, (payloadsizeincell-payloadheaderlen), overflowpageoffset, overflowpagenum

    def _parseLeafIndexCellHeader(self, data,offset):

        headerlist = list()
        overflowpageoffset = offset

        # Payload length
        payloadlen,length = self._getVarIntOfs(data, offset)
        offset+=length
        overflowpageoffset+=length
        # Payload Header Length
        payloadheaderlen,length = self._getVarIntOfs(data, offset)
        payloadheaderlenofs = offset + payloadheaderlen
        offset+=length

        # Overflow Page Number
        overflowpageoffset += self._getPayloadSizeInCell(payloadlen)
        overflowpageoffset = int(overflowpageoffset)
        if (payloadlen > (self.dbHeaderDict["pageSize"] - self.dbHeaderDict["unused_reserved_space"] - 35)):
            overflowpagenum = unpack(">I",data[overflowpageoffset:overflowpageoffset+4])[0]
        else:
            overflowpagenum = 0

        # Payload Fields
        while offset < (payloadheaderlenofs):
            fieldtype,length = self._getVarIntOfs(data, offset)
            # Determine Serial Type
            if fieldtype == 0:
                headerlist.append(("NULL",0))
            elif fieldtype == 1:
                headerlist.append(("ST_INT8",1))
            elif fieldtype == 2:
                headerlist.append(("ST_INT16",2))
            elif fieldtype == 3:
                headerlist.append(("ST_INT24",3))
            elif fieldtype == 4:
                headerlist.append(("ST_INT32",4))
            elif fieldtype == 5:
                headerlist.append(("ST_INT48",6))
            elif fieldtype == 6:
                headerlist.append(("ST_INT64",8))
            elif fieldtype == 7:
                headerlist.append(("ST_FLOAT",8))
            elif fieldtype == 8:
                headerlist.append(("ST_C0",0))
            elif fieldtype == 9:
                headerlist.append(("ST_C1",0))
            elif fieldtype > 11:
                if (fieldtype%2) == 0:
                    headerlist.append(("ST_BLOB",(fieldtype-12)/2))
                else:
                    headerlist.append(("ST_TEXT",(fieldtype-13)/2))
            else:
                headerlist.append(("Reserved: %s" % str(fieldtype),0))
            offset+=length

        return headerlist, payloadheaderlen, offset, payloadlen, overflowpageoffset, overflowpagenum

    def _parseInteriorTableCellHeader(self, data,offset):
        """
        Parse a B-Tree Leaf Page Cell Header, given it's starting absolute byte
        offset.
        Pass absolute starting byte offset for the cell header to be decoded.
        Returns tuple containing a list of tuples in the form
        [(String type,int length),...], and the starting offset of the payload
        fields.
        """
        headerlist = list()

        # pagenumleftchild length
        pagechildleftnum = unpack(">I",data[offset:offset+4])
        offset+=4
        # Record Number
        recordnum,length = self._getVarIntOfs(data, offset)
        offset+=length

        return headerlist, offset, pagechildleftnum[0], recordnum

    def _parseInteriorIndexCellHeader(self, data,offset):

        headerlist = list()
        overflowpageoffset = offset

        # pagenumleftchild length
        pagechildleftnum = unpack(">I",data[offset:offset+4])
        offset+=4

        # Payload length
        payloadlen,length = self._getVarIntOfs(data, offset)
        offset+=length
        overflowpageoffset+=length
        # Payload Header Length
        payloadheaderlen,length = self._getVarIntOfs(data, offset)
        payloadheaderlenofs = offset + payloadheaderlen
        offset+=length

        # Overflow Page Number
        overflowpageoffset += self._getPayloadSizeInCell(payloadlen)
        overflowpageoffset = int(overflowpageoffset)
        if (payloadlen > (self.dbHeaderDict["pageSize"] - self.dbHeaderDict["unused_reserved_space"] - 35)):
            overflowpagenum = unpack(">I",data[overflowpageoffset:overflowpageoffset+4])[0]
        else:
            overflowpagenum = 0

        # Payload Fields
        while offset < (payloadheaderlenofs):
            fieldtype,length = self._getVarIntOfs(data, offset)
            # Determine Serial Type
            if fieldtype == 0:
                headerlist.append(("NULL",0))
            elif fieldtype == 1:
                headerlist.append(("ST_INT8",1))
            elif fieldtype == 2:
                headerlist.append(("ST_INT16",2))
            elif fieldtype == 3:
                headerlist.append(("ST_INT24",3))
            elif fieldtype == 4:
                headerlist.append(("ST_INT32",4))
            elif fieldtype == 5:
                headerlist.append(("ST_INT48",6))
            elif fieldtype == 6:
                headerlist.append(("ST_INT64",8))
            elif fieldtype == 7:
                headerlist.append(("ST_FLOAT",8))
            elif fieldtype == 8:
                headerlist.append(("ST_C0",0))
            elif fieldtype == 9:
                headerlist.append(("ST_C1",0))
            elif fieldtype > 11:
                if (fieldtype%2) == 0:
                    headerlist.append(("ST_BLOB",(fieldtype-12)/2))
                else:
                    headerlist.append(("ST_TEXT",(fieldtype-13)/2))
            else:
                headerlist.append(("Reserved: %s" % str(fieldtype),0))
            offset+=length

        return headerlist, payloadheaderlen, offset, payloadlen, overflowpageoffset, overflowpagenum

    '''
    End of SQLiteZer functions
    '''

    def _unpack48(self, x):
        return int.from_bytes(x, byteorder='big')


def checkPythonVersion():
#    print(__import__("sys").version)
    PYTHONVERSION, = __import__("sys").version_info[:1]

    return PYTHONVERSION

#######################################################################################
#
# Main
#
#######################################################################################
def main(argv):

    usage = "Parse deleted records from an SQLite file \n\
            Examples:\n\
            -f /home/forensics/sms.db\n\
            -d debug\n\
            -l list all tables\n\
            -s print schema\n\
            -i print db info\n\
            -b print binary to stdout\n\
            -B print binary to file\n\
            -a print all\n\
            -F print freespace\n\
            -U print unallocated\n\
            -D print deleted pages\n\
            -p print table\n\
            -N tablename or\n\
            -n table number\n"


#    parser = OptionParser(usage=usage)
    parser = OptionParser(usage="%prog" + "\n" + usage, version="%prog " + VERSION + " (" + BUILD + ")")
    parser.add_option("-f", "--file", dest = "infile", help = "sqlite database file", metavar = "sms.db")
    parser.add_option("-d", "--debug", action ="store_true", dest = "debug", help = "Optional")
    parser.add_option("-l", "--tables", action ="store_true", dest = "listtables", help = "Optional")
    parser.add_option("-s", "--schema", action ="store_true", dest = "printschema", help = "Optional")
    parser.add_option("-i", "--info", action ="store_true", dest = "printinfo", help = "Optional")
    parser.add_option("-b", "--bin2out", action ="store_true", dest = "bin2out", help = "Optional")
    parser.add_option("-B", "--bin2file", action ="store_true", dest = "bin2file", help = "Optional")
    parser.add_option("-a", "--all", action ="store_true", dest = "printall", help = "Optional")
    parser.add_option("-m", "--map", action ="store_true", dest = "printmap", help = "Optional")


    group = OptionGroup(parser, "Print table", "Print dedicated table. Lookup a table name or number with option -l")
    group.add_option("-p", "--printtable", action ="store_true", dest = "printtable", help = "Optional")
    group.add_option("-N", "--table name",  dest = "tablename", help = "Optional")
    group.add_option("-n", "--table number", dest = "tablenum", help = "Optional")
    group.add_option("-F", "--freespace", action ="store_true", dest = "freespace", help = "Optional")
    group.add_option("-U", "--unallocated", action ="store_true", dest = "unallocated", help = "Optional")
    group.add_option("-D", "--deleted", action ="store_true", dest = "deleted", help = "Optional")

    parser.add_option_group(group)
#    parser.add_option("-p", "--printtable", action ="store_true", dest = "printtable", help = "Optional")
#    parser.add_option("-N", "--table name",  dest = "tablename", help = "Optional")
#    parser.add_option("-n", "--table number", dest = "tablenum", help = "Optional")



    (options,args)=parser.parse_args()

    if options.printall:
        options.freespace = True
        options.deleted = True
        options.unallocated = True

    if checkPythonVersion() != 3:
        print("SQLiteDBParser requires python version 3...")
        sys.exit(0)
#    else:
#        print("Python version ok...")

    #if input file missing, exit
    if (options.infile == None):
        parser.print_help()
        print( "Filename or Output file not given")
        sys.exit(0)

    #if file does not exist exit
    try:
        f=open(options.infile,"rb")
        f.close()
    except:
        print ("File not Found %s" %str(options.infile))
        sys.exit(0)

    sqliteDB = SQLiteDBParser(options)

    #exit if file is not a SQLite database
    if sqliteDB.isSqliteDB() == False:
        print ("File %s is not a regular sqlite database" %str(options.infile))
        sys.exit(0)

    if options.printall:
        sqliteDB.printDBheader()
        if sqliteDB.hasPtrMap() == True:
            sqliteDB.printPtrMap()
        sqliteDB.printDBSchema()
        sqliteDB.printDBData()
    if options.printinfo:
        sqliteDB.printDBheader()
    if options.printschema:
        sqliteDB.printDBSchema()
    if options.listtables:
        sqliteDB.listAllTables()
    if options.printtable == True:
        if options.tablename == None and options.tablenum == None:
            return
        if options.tablename:
            sqliteDB.printTable(name=options.tablename)
        if options.tablenum:
            sqliteDB.printTable(number=options.tablenum)
        pass
    if options.printmap == True:
        sqliteDB.printDBMap()

if __name__ == '__main__':
    main(sys.argv[1:])