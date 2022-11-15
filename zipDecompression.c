// Source: https://www.geeksforgeeks.org/c-program-to-read-and-print-all-files-from-a-zip-file/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <zip.h>
#include <zlib.h>

#define CHUNK 1000

// We need to change one line of the zlib library function
// uncompress2 from err = inflateInit(&stream); to err =
// inflateInit2(&stream, -MAX_WBITS);

// This tells function that there is no extra zlib, gzip, z
// header information It's just a pure stream of compressed
// data to decompress

int ZEXPORT uncompress2(dest, destLen, source, sourceLen)
                        Bytef* dest;
                        uLongf* destLen;
                        const Bytef* source;
                        uLong* sourceLen; {

    z_stream stream;
    int err;
    const uInt max = (uInt)-1;
    uLong len, left;

    // for detection of incomplete stream when *destLen == 0
    Byte buf[1];

    len = *sourceLen;

    if (*destLen) {

        left = *destLen;
        *destLen = 0;

    } else {

        left = 1;
        dest = buf;

    }

    stream.next_in = (z_const Bytef*)source;
    stream.avail_in = 0;
    stream.zalloc = (alloc_func)0;
    stream.zfree = (free_func)0;
    stream.opaque = (voidpf)0;

    err = inflateInit2(&stream, -MAX_WBITS); // THIS LINE IS CHANGED

    if (err != Z_OK) {

        return err;

    }
    
    stream.next_out = dest;
    stream.avail_out = 0;

    do {

        if (stream.avail_out == 0) {

            stream.avail_out = left > (uLong)max ? max : (uInt)left;            
            left -= stream.avail_out;

        }

        if (stream.avail_in == 0) {

            stream.avail_in = len > (uLong)max ? max : (uInt)len;
            len -= stream.avail_in;

        }

        err = inflate(&stream, Z_NO_FLUSH);

    } while (err == Z_OK);

    *sourceLen -= len + stream.avail_in;

    if (dest != buf) {

        *destLen = stream.total_out;

    } else if (stream.total_out && err == Z_BUF_ERROR) {

        left = 1;

    }

    inflateEnd(&stream);
    
    return err == Z_STREAM_END
               ? Z_OK
               : err == Z_NEED_DICT
                     ? Z_DATA_ERROR
                     : err == Z_BUF_ERROR
                               && left + stream.avail_out
                           ? Z_DATA_ERROR
                           : err;

}

int main(int argc, char* argv[]) {

    // example usage: ./program zipfile.zip

    if (argc > 2 || argc < 2) {

        return -1;

    }

    if (!fopen(argv[1], "r")) {

        return -2;
    
    }

    int errorp = 0; // error code variable    
    zip_t* arch = NULL; // Zip archive pointer
    arch = zip_open(argv[1], 0, &errorp);
    
    // allocates space for file information
    struct zip_stat* finfo = NULL;
    finfo = calloc(256, sizeof(int)); // must be allocated
    zip_stat_init(finfo);
    
    // Loop variables
    int index = 0;
    char* txt = NULL;
    zip_file_t* fd = NULL;
    char* outp = NULL;
    
    while (zip_stat_index(arch, index, 0, finfo) == 0) {
        
        txt = calloc(finfo->comp_size + 1, sizeof(char));
        // Read compressed data to buffer txt
        // ZIP_FL_COMPRESSED flag is passed in to read the
        // compressed data
        fd = zip_fopen_index(arch, 0, ZIP_FL_COMPRESSED);
        zip_fread(fd, txt, finfo->comp_size);

        outp = calloc(finfo->size + 1, sizeof(char));
        // uncompresses from txt buffer to outp buffer
        // uncompress function calls our uncompress2
        // function defined at top
        uncompress(outp, &finfo->size, txt, finfo->comp_size);

        printf("FILE #%i: %s\n", index + 1, finfo->name);
        printf("\n%s\n", outp);

        // free memory every iteration
        free(txt);
        free(outp);

        index++;

    }

}
