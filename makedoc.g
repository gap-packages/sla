##  this creates the documentation, needs: GAPDoc and AutoDoc packages, pdflatex
##
##  Call this with GAP from within the package directory.
##

if fail = LoadPackage("AutoDoc", ">= 2019.04.10") then
    Error("AutoDoc 2019.04.10 or newer is required");
fi;

AutoDoc(rec( scaffold := rec( MainPage := false ),
             extract_examples := rec( skip_empty_in_numbering := false ),
             gapdoc := rec( main := "manual.xml" )));
