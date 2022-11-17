from libzip import ZipFile

zObject = ZipFile("large.zip", 'r')

zObject.extractall()

zObject.close()
