SQLiteDBParser
==============

A forensic tool to parse SQLite databases.
Will recover deleted records, parse out
unallocated and freespace.

License : GNU GPL v2

How to use:
===========

Usage: SQLiteDBParser.py  

    Examples:  
            -f /home/forensics/sms.db  
            -d debug    
            -l list all tables  
            -s print schema  
            -i print db info  
            -a print all 
            -b print binary data to stdout
            -B print binary data to file
            -F print freespace  
            -U print unallocated  
            -D print deleted pages  
            -p print table  
            -N tablename or  
            -n table number  


   Options: 
      
    --version                show program's version number and exit
    -h, --help               show this help message and exit
    -f sms.db, --file=sms.db sqlite database file
    -d, --debug              Optional
    -l, --tables             Optional
    -s, --schema             Optional
    -i, --info               Optional
    -a, --all                Optional
    -b, --bin2out            Optional
    -B, --bin2file           Optional


  Print table:  
    Print dedicated table. Lookup a table name or number with option -l  

    -p, --printtable    Optional
    -N TABLENAME, --table name=TABLENAME
                        Optional
    -n TABLENUM, --table number=TABLENUM
                        Optional
    -F, --freespace     Optional
    -U, --unallocated   Optional
    -D, --printdeleted  Optional
