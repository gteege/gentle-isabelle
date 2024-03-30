ISABELLE=~/Isabelle2023/bin/isabelle

doc:
	$(ISABELLE) build -v -b -d . man-isabelle
	if [ -e output/document.pdf ]; then cp output/document.pdf man-isabelle.pdf; fi

clean:
	-rm -f *~
	-rm -r output


