block UnitIntegrator
    output Real x;
protected
    constant Real samplePeriod;
public
    method Startup
    algorithm
        self.x := 0.0;
        self.samplePeriod := 1.0;
    end Startup;
    method Recalibrate
    algorithm
    end Recalibrate;
    method DoStep
    algorithm
        self.x := (self.x + 1.0);
    end DoStep;
end UnitIntegrator;
