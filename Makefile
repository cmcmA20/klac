.PHONY: test Everything.agda clean

OTHEROPTS = --auto-inline -Werror

RTSARGS = +RTS -M6G -A128M -RTS ${OTHEROPTS}

test: Everything.agda
	agda ${RTSARGS} -i. Everything.agda

html: Everything.agda
	agda ${RTSARGS} --html -i. Everything.agda

Everything.agda:
	git ls-tree --full-tree -r --name-only HEAD | grep --exclude-dir=src/homework/ '^src/[^\.]*.[agda|lagda.org]' | sed -e 's|^src/[/]*|import |' -e 's|/|.|g' -e 's/.lagda.org//' -e 's/.agda//' -e '/import Everything/d' | grep -v '.png' | grep -v 'homework' | LC_COLLATE='C' sort > Everything.agda

clean:
	find . -name '*.agdai' -exec rm \{\} \;
