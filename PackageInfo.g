#############################################################################
##  
##  PkgInfo file for the package SLA               Willem de Graaf
##  

SetPackageInfo( rec(
PackageName := "SLA",
Subtitle := "a package for doing computations with simple Lie algebras",        
Version := "1.2",
Date := "01/11/2016",
ArchiveURL := Concatenation("http://www.science.unitn.it/~degraaf/sla/sla-",
                            ~.Version),
ArchiveFormats := ".tar.gz",
Persons := [
  rec(
  LastName := "de Graaf",
  FirstNames := "Willem Adriaan",
  IsAuthor := true,
  IsMaintainer := true,
  Email := "degraaf@science.unitn.it",
  WWWHome := "http://www.science.unitn.it/~degraaf",
  Place := "Trento",
  Institution := "Dipartimento di Matematica"
  )
],
Status := "accepted",
CommunicatedBy := "Leonard Soicher (QMUL)",
AcceptDate := "01/2016",
README_URL := 
  "http://www.science.unitn.it/~degraaf/sla/README.sla",
PackageInfoURL := 
  "http://www.science.unitn.it/~degraaf/sla/PackageInfo.g",
AbstractHTML := "The package <span class=\"pkgname\">SLA</span> contains \
                 functionality for working with simple Lie algebras,",
PackageWWWHome := "http://www.science.unitn.it/~degraaf/sla.html",
Dependencies := rec(
  GAP := ">=4.3",
  NeededOtherPackages:= [["quagroup", ">=1.3" ]],                 
  SuggestedOtherPackages := [ ["GAPDoc", ">= 1.0"] ],
  ExternalConditions := []
),
PackageDoc := rec(
  BookName  := "SLA",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Computing with simple Lie algebras",
  Autoload  := true
),

AvailabilityTest := ReturnTrue,
Autoload := false,

# the banner
#BannerString := 
#"     SLA --- computations with Simple Lie Algebras \n",
Keywords := ["simple Lie algebras","representation tehory"]
));
