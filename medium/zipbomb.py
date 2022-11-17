from libzip import ZipFile

zObject = ZipFile("medium.zip", 'r')

zObject.extractall()

zObject.close()
