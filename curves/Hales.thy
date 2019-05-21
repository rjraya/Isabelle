theory Hales
  imports Main
begin

fun e where
 "e x y = 

e[x_, y_] := (x^2 + c y^2 - 1 - d x^2 y^2);
{e1, e2, e3} = {e[x1, y1], e[x2, y2], e[x3, y3]};

z0 = {x0,y0};
z1 = {x1,y1};
z2 = {x2,y2};
z3 = {x3,y3};

ez[{x_,y_}]:= e[x,y];
{e0,e1,e2,e3} = {ez[z0],ez[z1],ez[z2],ez[z3]};

fun delta where
 "delta x1 y1 x2 y2 = 1 - d^2*x1^2*x2^2*y1^2*y2^2"


end