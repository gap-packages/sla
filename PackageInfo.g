#############################################################################
##
##  PkgInfo file for the package SLA               Willem de Graaf
##

SetPackageInfo( rec(
PackageName := "SLA",
Subtitle := "Computing with simple Lie algebras",
Version := "1.6.2",
Date := "12/07/2024", # dd/mm/yyyy format
License := "GPL-2.0-or-later",

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
  ),
  rec(
    LastName      := "GAP Team",
    FirstNames    := "The",
    IsAuthor      := false,
    IsMaintainer  := true,
    Email         := "support@gap-system.org",
  ),
],
Status := "accepted",
CommunicatedBy := "Leonard Soicher (QMUL)",
AcceptDate := "01/2016",

PackageWWWHome  := "https://gap-packages.github.io/sla/",
README_URL      := Concatenation( ~.PackageWWWHome, "README.md" ),
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/gap-packages/sla",
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/sla-", ~.Version ),
ArchiveFormats := ".tar.gz",

AbstractHTML := "The package <span class=\"pkgname\">SLA</span> contains \
                 functionality for working with simple Lie algebras,",

Dependencies := rec(
  GAP := ">=4.12",
  NeededOtherPackages:= [["quagroup", ">=1.8" ]],
  SuggestedOtherPackages := [],
  ExternalConditions := []
),
PackageDoc := rec(
  BookName  := "SLA",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0_mj.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Computing with simple Lie algebras",
  Autoload  := true
),

AvailabilityTest := ReturnTrue,
TestFile := "tst/testall.g",
Keywords := ["simple Lie algebras","representation theory"],

AutoDoc := rec(
    TitlePage := rec(
        Version := Concatenation( "Version ", ~.Version ),
        Abstract := """
            This package provides functions for computing with various
            aspects of the theory of simple Lie algebras in characteristic
            zero.
            """,
        Copyright := "&copyright; 2013-2018 Willem de Graaf",
    ),
),

));
