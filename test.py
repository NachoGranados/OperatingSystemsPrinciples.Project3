from libzip2 import ZipFile

zObject = ZipFile("zipTest.zip", 'r')

zObject.extractall()

zObject.close()
