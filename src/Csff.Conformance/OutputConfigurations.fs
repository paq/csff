namespace Csff.Conformance

open Csff.Printer

module OutputConfigurations =
    let all =
        [
            for width in [ 40; 55; 60; 70; 80; 90; 100; 120; 150; 200 ] do
                yield
                    $"width {width}, spaces",
                    { PrinterOptions.Default with
                        Width = width
                    }
            yield
                "width 100, tabs",
                { PrinterOptions.Default with
                    UseTabs = true
                }
        ]
