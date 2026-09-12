use std::io::{self, BufRead, Write};

fn main() -> io::Result<()> {
    let input = io::stdin();
    let mut output = io::BufWriter::new(io::stdout().lock());
    for line in input.lock().lines() {
        writeln!(output, "{}", ephemeris_reference::fuzz::respond(&line?))?;
    }
    output.flush()
}
