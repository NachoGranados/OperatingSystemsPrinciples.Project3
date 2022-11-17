from libzip import ZipFile

zObject = ZipFile("small.zip", 'r')

zObject.extractall()

zObject.close()
