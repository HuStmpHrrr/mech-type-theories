from bs4 import BeautifulSoup
import sys

FILE = sys.argv[1]
with open(FILE) as fd:
    soup = BeautifulSoup(fd, "html.parser")

body = soup.select_one('body')
body.contents = [
    e.wrap(soup.new_tag("div", attrs={"class": "main"})) for e in body]
t = BeautifulSoup(
    '<div class="navbar"><a class="active" href="README.html">Everything</a><a style="float:right" href="index.html">Home</a></div>', "html.parser")
body.insert(0, t.div)

with open(FILE, 'w') as fd:
    fd.write(str(soup))
