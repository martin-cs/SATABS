input rboxes

verbatimtex
  %&latex
  \documentclass{article}
  \usepackage{helvet}
  \begin{document}
  \sffamily
  etex

rbox_radius := 3bp;

diamond_radius := 5bp;

vardef doall(expr Cabs, Cmc, Csim, Cref)=
  rboxit.abstract (btex $\matrix{\mathsf{1.)\;Compute}\cr\mathsf{Abstraction}}$  etex);
  rboxit.check (btex $\matrix{\mathsf{2.)\;Check}\cr\mathsf{Abstraction}}$ etex);
  rboxit.feasible (btex $\matrix{\mathsf{3.)\;Check}\cr\mathsf{Feasibility}}$ etex);
  rboxit.refine (btex $\matrix{\mathsf{4.)\;Refine}\cr\mathsf{Predicates}}$ etex);

  abstract.c = (0,2cm);
  check.c = (4cm,2cm);
  feasible.c = (4cm,0);
  refine.c = (0,0);
  
  abstract.se - abstract.nw = check.se -  check.nw = feasible.se - feasible.nw = refine.se - refine.nw;

  fill bpath abstract withcolor Cabs;
  fill bpath check withcolor Cmc;
  fill bpath feasible withcolor Csim;
  fill bpath refine withcolor Cref;

  drawboxed (abstract, check, feasible, refine);
  
  pair diamok;
  diamok = ((xpart check.ne)+12pt,1cm);
  draw diamok+(0,diamond_radius)--diamok+(diamond_radius,0)--diamok+(0,-diamond_radius)--diamok+(-diamond_radius,0)--cycle;
 
  drawarrow (.5[abstract.nw,abstract.ne])..0.5[abstract.c,check.c] shifted (0,1cm)..(.5[check.nw,check.ne]) cutbefore bpath.abstract cutafter bpath.check;

  drawarrow .5[check.ne,check.se]..(.5[check.ne,check.se] shifted (4pt,-4pt))..diamok+(0,diamond_radius) cutbefore bpath.check;
  
  drawarrow diamok+(0,-diamond_radius)..(.5[feasible.ne,feasible.se] shifted (4pt,4pt))..(.5[feasible.ne,feasible.se]) cutafter bpath.feasible;

  drawarrow diamok+(diamond_radius,0)--diamok+(diamond_radius+2cm,0);
  label.top (btex [no error] etex, diamok+(diamond_radius+1cm,0));
  label.rt (btex OK etex, diamok+(diamond_radius+2cm,0));

  pair diamnok;
  diamnok = (2cm,(ypart feasible.sw)-12pt);
  draw diamnok+(0,diamond_radius)--diamnok+(diamond_radius,0)--diamnok+(0,-diamond_radius)--diamnok+(-diamond_radius,0)--cycle;

  drawarrow (.5[feasible.se,feasible.sw])..(.5[feasible.se,feasible.sw] shifted (-4pt,-2pt))..diamnok+(diamond_radius,0) cutbefore bpath.feasible;

  drawarrow diamnok+(-diamond_radius,0)..(.5[refine.se,refine.sw] shifted (4pt,-2pt))..(.5[refine.se,refine.sw]) cutafter bpath.refine;

  drawarrow (.5[refine.nw,refine.sw])..(.5[abstract.sw,refine.nw]-(10pt,0))  ..(.5[abstract.nw,abstract.sw]);

  drawarrow diamnok+(0,-diamond_radius)--diamnok+(0,-diamond_radius-1cm);
  label.rt (btex [feasible] etex, diamnok+(0,-diamond_radius-0.5cm));
  label.bot (btex report counterexample etex, diamnok+(0,-diamond_radius-1cm));

  drawarrow abstract.nw+(-0.5cm,0.5cm)--abstract.nw cutafter bpath.abstract;
  label.top (btex C program etex, abstract.nw+(-0.5cm,0.5cm));
enddef;

color Chighlight;
Chighlight := (0.98824, 0.91373, 0.30980);

beginfig(1)
  doall(white, white, white, white);
endfig;

beginfig(2)
  doall(Chighlight, white, white, white);
endfig;

beginfig(3)
  doall(white, Chighlight, white, white);
endfig;

beginfig(4)
  doall(white, white, Chighlight, white);
endfig;

beginfig(5)
  doall(white, white, white, Chighlight);
endfig;

end.
