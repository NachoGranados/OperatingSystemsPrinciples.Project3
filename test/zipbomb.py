from libzip import ZipFile

zObject = ZipFile("test.zip", 'r')

zObject.extractall()

zObject.close()
