model ArrayDriven
  input Real u[2];
  output Real x[2](each start=0, each fixed=true);
equation
  der(x) = u;
end ArrayDriven;
