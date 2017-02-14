default:
	jekyll build

clean:
	jekyll clean

serve:
	jekyll serve

publish: default
	rsync -rcpv --chmod=a+r _site/ swier004@csstaff-new.science.uu.nl:/users/www/docs/vakken/afp


