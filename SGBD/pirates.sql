create table navires (
    CodeNav int PRIMARY KEY,
    RayonAction float not null check(RayonAction >= 0.0),
    NbPilotes int not null check(NbPilotes > 0),
    Vmax float not null check(Vmax > 0.0)
);

create table pilotes (
    CodeP int PRIMARY KEY,
    NomPil char not null,
    PrenomPil char not null,
    Age int not null check(Age >= 18),
    Grade char not null
);

create table typeMission (
    TypeMis char check(TypeMis in ('transport', 'combat', 'interception', 'pillage')) PRIMARY KEY
)

create table missions (
    CodeMis int PRIMARY KEY,
    DateMis DATE not null,
    Vmin float not null check(Vmin > 0.0),
    RayonEng float not null check(RayonEng > 0.0),
    NbNav int not null check(NbNav > 0),
    TypeMis char not null references typeMission(TypeMis)
);

create table equipage(
    CodeEq int PRIMARY KEY,
    Effectif int not null check(Effectif > 0)
);

create table milieu (
    Composition char check(Composition in ('acide', 'basique', 'neutre')) PRIMARY KEY
);

create table galaxies (
    CodeGal int PRIMARY KEY,
    NomGalaxie char not null,
    Distance int not null check(Distance > 0)
);

create table planetes (
    CodeGal int not null references galaxies(CodeGal),
    CodePla int not null,
    NomPla char not null,
    Vlib float not null check(Vlib > 0.0),
    Statut char not null check(Statut in ('non-exploree', 'reconnue', 'integree')),
    Composition char not null references milieu(Composition),
    PRIMARY KEY (CodeGal, CodePla)
);

create table naviresTransport (
    CodeNav int PRIMARY KEY references navires(CodeNav),
    RayonAction float not null,
    NbPilotes int not null,
    Vmax float not null,
    Capacite float not null
);

create table naviresTransport (
    CodeNav int PRIMARY KEY references navires(CodeNav),
    RayonAction float not null,
    NbPilotes int not null,
    Vmax float not null,
    Tmin float not null,
    Tmax float not null,
    check(Tmin <= Tmax)
);

create table peutcibler (
    CodeMis int PRIMARY KEY references missions(CodeMis), 
    CodePla int not null
    CodeGal int not null
    foreign key (CodeGal, CodePla) references planetes(CodeGal, CodePla)
);

create table formepar (
    CodeP int not null references pilotes(CodeP),
    TypeMis char not null references typeMission(TypeMis),
    PRIMARY KEY (CodeP, TypeMis)
);

create table peutremplir (
    CodeEq int not null references equipage(CodeEq),
    TypeMis char not null references typeMission(TypeMis),
    PRIMARY KEY (CodeEq, TypeMis)
);

create table affectationequipage (
    CodeNav int not null references navires(CodeNav),
    CodeEq int not null references equipage(CodeEq),
    CodeMis int not null references missions(CodeMis),
    PRIMARY KEY (CodeNav, CodeEq, CodeMis)
);

create table affectationpilote (
    CodeNav int not null references navires(CodeNav),
    CodeP int not null references pilotes(CodeP),
    CodeMis int not null references missions(CodeMis),
    PRIMARY KEY (CodeNav, CodeP, CodeMis)
);

create table adaptea (
    CodeNav int not null references navires(CodeNav),
    Composition char not null references milieu(Composition),
    PRIMARY KEY (CodeNav, Composition)
);

create table qualifiepour (
    CodeNav int not null references navires(CodeNav),
    CodeP int not null references pilotes(CodeP),
    PRIMARY KEY (CodeNav, CodeP)
);

create table affectationnavires (
    CodeNav int not null references navires(CodeNav),
    CodeMis int not null references missions(CodeMis),
    PRIMARY KEY (CodeNav, CodeMis)
);

-- mettre en commentaire les contraintes de contexte