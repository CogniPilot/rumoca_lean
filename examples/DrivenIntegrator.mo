model DrivenIntegrator
  input Real u;
  output Real x(start=0, fixed=true);
equation
  der(x) = u;
end DrivenIntegrator;
