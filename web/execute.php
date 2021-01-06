<?php

$prog_text = filter_input(INPUT_POST, "code", FILTER_UNSAFE_RAW);
$rooplpp_flags = array("-t30");

$invert = filter_input(INPUT_POST, "invert", FILTER_VALIDATE_BOOLEAN);
$compile = filter_input(INPUT_POST, "compile", FILTER_VALIDATE_BOOLEAN);

if ($invert === TRUE) {
  array_push($rooplpp_flags, "-i");
}
if ($compile === TRUE) {
  array_push($rooplpp_flags, "-c");
}

# Read program from stdin
array_push($rooplpp_flags, "-");

$dir = dirname(__FILE__);
$cmd = "$dir/ROOPLPP " . implode(" ", $rooplpp_flags);

$cwd = "/tmp";
$descriptorspec = array(
    0 => array("pipe", "r"),
    1 => array("pipe", "w")
);
$env = array();

$process = proc_open($cmd, $descriptorspec, $pipes, $cwd, $env);

if (is_resource($process)) {

    fwrite($pipes[0], $prog_text);
    fclose($pipes[0]);

    $output = stream_get_contents($pipes[1]);
    fclose($pipes[1]);

    $return_value = proc_close($process);

    echo $return_value . "\n";

    if ($return_value === 100) {
      echo "Execution timed out!\n";
    }
    echo $output;
}

?>
