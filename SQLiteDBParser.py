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
#
# Limitations: sql command parser is not working 100% correctly
#              matching of deleted pages to tables only based on column count
#                  matching of column type and cell content is missing
#              output is not really nice
#              pointer maps are not handled correctly
#              blob data is not supported
#              overflow pages are not supported
#              index tables are not supported
#
# Requires:    Python 3
#
# Created:     19/08/2015
# License:     GPL v2.0
#-------------------------------------------------------------------------------

__author__ = 'grisomg'

from struct import unpack
from optparse import OptionParser, OptionGroup
import sys

VERSION = '0.8'
BUILD = '20150819'

GPLNOTICE = '   Copyright (C) 2015 GrisoMG\n\
    This program comes with ABSOLUTELY NO WARRANTY\n\
    This is free software, and you are welcome to redistribute it\n\
    under certain conditions'

SQLITE_SIGNATURE = b'SQLite format 3\x00'

INTERIOR_INDEX_BTREE_PAGE = 2
INTERIOR_TABLE_BTREE_PAGE = 5
LEAF_INDEX_BTREE_PAGE = 10
LEAF_TABLE_BTREE_PAGE = 13

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

    def __init__(self, sqlitedb):

        self.sqlitedb = sqlitedb
        self.data = b''
        self.pageOffsets = []
        self.dbInfo = dict()
        self.dbHeaderDict = dict()
        self.ptrMap = list()
        self.dbSchema = {}
        self.dbPages = []
        self.lPagesWithoutRoot = []

        # 1. read db file, parse header, check if valid sqlite database, parse schema, get page offsets
        self._readDBFile()
        self._parseDBHeader()
        if self.isSqliteDB() == False:
            return None

        self.dbSchema = self._parseDBSchema(self.data[:self.dbHeaderDict["pageSize"]])
        self._getPageOffsets()

        # 2. read all pages
        self._readallDBPages()
        self._setSchemaForRootPages()

        # 3. are all leaf pages assigned to a root page? if not try to find a mapping root page by mapping schema
        self._lPagesWithoutRoot()

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
                self.dbPages[rootNr]["deletedpages"] = list()
                self.dbPages[rootNr]["deletedpages"].append(pageNr)

    def _findMatchingSchema(self, celldata):
        #compare number of columns with schema of tables
        #col type are not checked at the moment ;-(
        num_of_cols = celldata[0].__len__()
        possibleschemalist = list()
        for schema in self.dbSchema:
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

        while i < buf.__len__():
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

        pageHeader = []
        pageDict = {}
        counter = 0
        for offset in self.pageOffsets:
            dbpage = {}
            pageNr += 1

            page = self.data[offset: offset + pageSize]

            if pageNr == 2 and self.dbHeaderDict["incremental_vacuum"] > 0:
                #in this case, the page is a pointer map
                self._readPointerMap(page)

            pageHeader = self._parsePageHeader(page, pageNr)
            dbpage["page"] = page
            dbpage["pageNr"] = pageNr
            dbpage["pageHeader"] = pageHeader
            dbpage["isRootPage"] = False

            dbpage["celldata"] = list()
            dbpage["deleteddata"] = list()

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

            if pageNr > 1 and dbpage["pageHeader"]["pageByte"] == INTERIOR_TABLE_BTREE_PAGE:
                dbpage["leafpages"] = self._readLeafPageList(dbpage, offset)
                dbpage["hasLeafPages"] = True
            dbpage["unallocated"] = self._readPageUnallocated(dbpage)
            dbpage["freespace"] = self._readPageFreeSpace(dbpage)

            if (dbpage["pageHeader"]["pageByte"] == LEAF_TABLE_BTREE_PAGE) and (dbpage["pageHeader"]["cellQty"] > 0):
                dbpage["celldata"] = self._readPageCells(dbpage, offset)


            pageDict[pageNr] = dbpage
            offset += pageSize
        self.dbPages = pageDict

    def _readPageCells(self, dbpage, offset):
        celldatalist = list()
        for cp in range(0,(dbpage["pageHeader"]["cellQty"]*2),2):
            celldata = list()
            start = cp
            end = cp + 2
            cellp = unpack('>H', dbpage["cellPointer"][start:end])[0]
            cellstart = offset + cellp
            celldata = self._parseCell(self.data, cellstart)
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
        while fbOffset > 0:
            try:
                start, size = unpack('>hh', dbpage["page"][fbOffset: fbOffset + 4])
                if size > 0:
                    freeblock = dbpage["page"][fbOffset: fbOffset + size]
                else:
                    freeblock = ''
                freeblocklist.append(freeblock)
                if (fbOffset != start) and (start > 0):
                    fbOffset = start
                else:
                    fbOffset = 0
                '''
                fbOffset = start
                '''
            except:
                fbOffset = 0
        return freeblocklist

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
            f=open(self.sqlitedb,"rb")
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
           rmpointer = unpack(self._ibtreefrmt, page[8:12])[0]
        else:
            rmpointer = None

        pageHeader = list(pageHeader)
        pageHeader.append(rmpointer)
        pageDict = dict(zip(self._btreehdrkeys, pageHeader))
        return pageDict

    def _parseDBHeader(self):
        self.dbHeaderDict = dict(zip(self._dbhdrkeys,list(self._unpackDBHeader())))

    def _parseDBSchema(self, buf):
        # based on https://github.com/n0fate/walitean
        TABLE = b'table'
        CREATETABLE = b'CREATE TABLE'
        dbschema = {}
        columnsdic = {}
        tables = []
        dbtable = {}
        tables = buf.split(TABLE)
        tables.pop(0)   # because I can not determine the right starting point
        for table in tables:
            columnlst = []
            dbtable = {}
            tbl_name = None
            tbl_rootpage = None
            strcolumns = None
            tbl_name, schema = table.split(CREATETABLE)#[0].decode()
            tbl_rootpage = unpack('B',tbl_name[tbl_name.__len__()-1:])[0]
            tbl_name = tbl_name[:tbl_name.__len__()-1]
            tbl_name = tbl_name[:int(tbl_name.__len__() / 2)]
            tbl_name = tbl_name.decode()
            dbtable['name'] = tbl_name
            dbtable['rootpage'] = tbl_rootpage
            strcolumns = self._findSQLCmd(schema)
            if strcolumns == "ERROR":
                continue
            l = strcolumns.find(b'UNIQUE (')
            r = strcolumns.find(b')')
            if l > 0 and r > l:
                strcolumns = strcolumns[:l-1] + strcolumns[r+1:]
            strcolumns = strcolumns.decode()

            if strcolumns[0] == ' ':    # remove byte if first byte is space
                strcolumns = strcolumns[1:]
            strcolumns = strcolumns.replace(' REFERENCES','')
            for column in strcolumns.split(','):
                if column[0] == ' ':
                    column = column[1:]
                if str(column).startswith('PRIMARY'):
                    continue
                try:
                    column.index('UNIQUE (')
                    continue
                except ValueError:
                    pass
                columninfo = []
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
            columnsdic[tbl_name] = dbtable
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

    def printDBheader(self):

        if self.dbHeaderDict["pageSize"] == 1:
            print("Page size in bytes:\t: 65536")
        else:
            print("Page size in bytes:\t%s" %str(self.dbHeaderDict["pageSize"]))
        print("write_version: %s" %str(self.dbHeaderDict["write_version"]))
        print("read_version: %s" %str(self.dbHeaderDict["read_version"]))
        print("unused_reservered_space: %s" %str(self.dbHeaderDict["unused_reserved_space"]))
        print("maximum_embedded_payload_fraction: %s" %str(self.dbHeaderDict["maximum_embedded_payload_fraction"]))
        print("minimum_embedded_payload_fraction: %s" %str(self.dbHeaderDict["minimum_embedded_payload_fraction"]))
        print("leaf_payload_fraction: %s" %str(self.dbHeaderDict["leaf_payload_fraction"]))
        print("file_change_counter: %s" %str(self.dbHeaderDict["file_change_counter"]))
        print("in_header_database_size: %s" %str(self.dbHeaderDict["in_header_database_size"]))
        print("first_freelist_trunk_page: %s" %str(self.dbHeaderDict["first_freelist_trunk_page"]))
        print("total_num_freelist_pages: %s" %str(self.dbHeaderDict["total_num_freelist_pages"]))
        print("schema_cookie: %s" %str(self.dbHeaderDict["schema_cookie"]))
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

        print("schema_format_number: %s\t=> %s" %(str(self.dbHeaderDict["schema_format_number"]),sf))
        print("default_page_cache_size: %s" %str(self.dbHeaderDict["default_page_cache_size"]))
        print("largest_root_b_tree: %s" %str(self.dbHeaderDict["largest_root_b_tree"]))

        if self.dbHeaderDict["database_text_encoding"] == 1:
            te = "UTF-8"
        elif self.dbHeaderDict["database_text_encoding"] == 2:
            te = "UTF-16le"
        elif self.dbHeaderDict["database_text_encoding"] == 3:
            te = "UTF-16be"
        else:
            te = "Invalid Text Encoding!"
        print("database_text_encoding: %s\t=> %s" %(str(self.dbHeaderDict["database_text_encoding"]),te))
        print("user_version: %s" %str(self.dbHeaderDict["user_version"]))
        print("incremental_vacuum: %s" %str(self.dbHeaderDict["incremental_vacuum"]))
        print("application_id: %s" %str(self.dbHeaderDict["application_id"]))
        print("reserved: %s" %str(self.dbHeaderDict["reserved"]))
        print("version_valid_for_number: %s" %str(self.dbHeaderDict["version_valid_for_number"]))

        print("sqlite_version_number: %s => %s" %(str(self.dbHeaderDict["sqlite_version_number"]),str(self.dbHeaderDict["sqlite_version_number"]).replace("00","0").replace("0",".")))

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
        for dbtable in self.dbSchema:
            print("Table: %s" %str(dbtable))
            print("\tTable name: %s" %str(self.dbSchema[dbtable]['name']))
            print("\tRoot page: %s" %str(self.dbSchema[dbtable]['rootpage']))
            print("\tSchema:")
            for key, value in self.dbSchema[dbtable]['schema']:
                print("\t\t %s:\t%s" %(str(key),str(value)))

    def printDBData(self, debug=None, verbose=None):
        if debug is not None:
            debug = True
        if verbose is not None:
            verbose = True

        for ipage in self.dbPages:
            if ipage == 1:
                continue

            self.printTable(number=ipage, verbose=verbose, debug=debug, fspace=True, unallocated=True, deleted=True)


    def printTable(self, name=None, number=None, debug=None, verbose=None, fspace=None, unallocated=None, deleted=None):
        page = None
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
            except:
                tblname = "???"
                colheader = "???"
            print("PageNr: %s\tTable name: %s" %(str(page["pageNr"]),str(tblname)))
            hdr = "Page;Type;"
            hdr += ";".join(map(str,colheader))
            print(hdr)

        if self.hasCelldata(page) == True:
            for row in page["celldata"]:
                rowdata = str(page["pageNr"]) + ";C;'"
                rowdata += "';'".join(map(str,row))
                rowdata += "'"
                print(rowdata)
        if fspace:
            for freespace in page["freespace"]:
                if verbose == True:
                    print(str(page["pageNr"]) + ";F;'';" + "'" + freespace + "'")
                else:
                    print(str(page["pageNr"]) + ";F;'';" + "'" + self._remove_non_printable(freespace) + "'")
        if unallocated:
            if verbose == True:
                print(str(page["pageNr"]) + ";U;'';" + "'" + page["unallocated"] + "'")
            else:
                data = self._remove_non_printable(page["unallocated"])
                if data != "":
                    print(str(page["pageNr"]) + ";U;'';" + "'" + data + "'")

        if self.hasLeafPages(page) == True:
            for leafpage in page["leafpages"]:
                if self.hasCelldata(self.dbPages[leafpage]) == True:
                    for row in self.dbPages[leafpage]["celldata"]:
                        rowdata = str(leafpage) + ";C;'"
                        rowdata += "';'".join(map(str,row))
                        rowdata += "'"
                        print(rowdata)
                if fspace and self.hasFreespace(self.dbPages[leafpage]) == True:
                    for freespace in self.dbPages[leafpage]["freespace"]:
                        if verbose == True:
                            print(str(leafpage) + ";F;'';" + "'" + str(freespace) + "'")
                        else:
                            print(str(leafpage) + ";F;'';" + "'" + self._remove_non_printable(freespace) + "'")
                if unallocated and self.hasUnallocated(self.dbPages[leafpage]) == True:
                    if verbose == True:
                        print(str(leafpage) + ";U;'';" + "'" + self.dbPages[leafpage]["unallocated"] + "'")
                    else:
                        data = self._remove_non_printable(self.dbPages[leafpage]["unallocated"])
                        if data != "":
                            print(str(leafpage) + ";U;'';" + "'" + data + "'")

        if deleted and self.hasDeleted(page) == True:
            for deletedpage in page["deletedpages"]:
                if self.hasCelldata(self.dbPages[deletedpage]) == True:
                    for row in self.dbPages[deletedpage]["celldata"]:
                        rowdata = str(deletedpage) + ";DC;'"
                        rowdata += "';'".join(map(str,row))
                        rowdata += "'"
                        print(rowdata)
                if fspace and self.hasFreespace(self.dbPages[deletedpage]) == True:
                    for freespace in self.dbPages[deletedpage]["freespace"]:
                        if verbose == True:
                            print(str(deletedpage) + ";DF;'';" + "'" + freespace + "'")
                        else:
                            print(str(deletedpage) + ";DF;'';" + "'" + self._remove_non_printable(freespace) + "'")

                if unallocated and self.hasUnallocated(self.dbPages[deletedpage]) == True:
                    if verbose == True:
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

        for dbtable in self.dbSchema:
            tbl_name = self.dbSchema[dbtable]['name']
            pageNr = self.dbSchema[dbtable]['rootpage']
            pageType = self.dbPages[pageNr]['pageType']
            col_count = 0
            try:
                col_count = self.dbSchema[dbtable]['schema'].__len__()
            except:
                pass

            print("Page number: %5s Table name: %20s Page Type: %23s Cols: %5s" %(str(pageNr), str(tbl_name), str(pageType), str(col_count)))

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

    def _parseCell(self, data,offset):
        """
        Parse a B-Tree Leaf Page Cell, given it's starting absolute byte offset.
        Pass absolute starting byte offset for the cell header.
        Returns the parsed cell as a list in the form:

        """
        celldatalist = list()
        cellheader,dataoffset,payloadlen,recordnum = self._parseCellHeader(data, offset)

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
                celldatalist.append("ST_INT48 - NOT IMPLEMENTED!") # NOT IMPLEMENTED YET!
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

        return celldatalist

    def _parseCellHeader(self, data,offset):
            """
            Parse a B-Tree Leaf Page Cell Header, given it's starting absolute byte
            offset.
            Pass absolute starting byte offset for the cell header to be decoded.
            Returns tuple containing a list of tuples in the form
            [(String type,int length),...], and the starting offset of the payload
            fields.
            """
            headerlist = list()

            # Payload length
            payloadlen,length = self._getVarIntOfs(data, offset)
            offset+=length
            # Record Number
            recordnum,length = self._getVarIntOfs(data, offset)
            offset+=length
            # Payload Header Length
            payloadheaderlen,length = self._getVarIntOfs(data, offset)
            payloadheaderlenofs = offset + payloadheaderlen
            offset+=length
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

            return headerlist, offset, payloadlen, recordnum
    '''
    End of SQLiteZer functions
    '''

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
    parser.add_option("-a", "--all", action ="store_true", dest = "printall", help = "Optional")

    group = OptionGroup(parser, "Print table", "Print dedicated table. Lookup a table name or number with option -l")
    group.add_option("-p", "--printtable", action ="store_true", dest = "printtable", help = "Optional")
    group.add_option("-N", "--table name",  dest = "tablename", help = "Optional")
    group.add_option("-n", "--table number", dest = "tablenum", help = "Optional")
    group.add_option("-F", "--freespace", action ="store_true", dest = "freespace", help = "Optional")
    group.add_option("-U", "--unallocated", action ="store_true", dest = "unallocated", help = "Optional")
    group.add_option("-D", "--printdeleted", action ="store_true", dest = "deleted", help = "Optional")

    parser.add_option_group(group)
#    parser.add_option("-p", "--printtable", action ="store_true", dest = "printtable", help = "Optional")
#    parser.add_option("-N", "--table name",  dest = "tablename", help = "Optional")
#    parser.add_option("-n", "--table number", dest = "tablenum", help = "Optional")



    (options,args)=parser.parse_args()

    if checkPythonVersion() != 3:
        print("SQLiteDBParser requires python version 3...")
        sys.exit(0)
    else:
        print("Python version ok...")

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

    sqliteDB = SQLiteDBParser(options.infile)

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
            sqliteDB.printTable(name=options.tablename, debug=options.debug, fspace=options.freespace, unallocated=options.unallocated, deleted=options.deleted)
        if options.tablenum:
            sqliteDB.printTable(number=options.tablenum, debug=options.debug, fspace=options.freespace, unallocated=options.unallocated, deleted=options.deleted)
        pass
if __name__ == '__main__':
    main(sys.argv[1:])