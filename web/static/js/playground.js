$(function(){
  editor = ace.edit("editor");
  editor.setTheme("ace/theme/tomorrow");
  editor.setShowPrintMargin(false);
  editor.getSession().setMode("ace/mode/roopl");
  editor.getSession().setTabSize(4);
  editor.getSession().setUseSoftTabs(true);
  editor.commands.addCommand({
    name: 'runCommand',
    bindKey: {win: 'Ctrl-Enter',  mac: 'Command-Enter'},
    exec: function(editor) {
        execute();
    },
    readOnly: true // false if this command should not apply in readOnly mode
  });

  var $editor = $("#editor");
  var $outputPane = $("#output-pane");
  var $output = $("#output");
  var $executing = $("#output-pane .executing");

  function setEditorContent(code) {
    editor.setValue(code);
    editor.gotoLine(0);
    removeErrorMarkers();
  }

  function loadCode(hash) {
    var match = hash.match(/#examples\/([a-zA-Z0-9-]+)/);
    if (match) {
      $.get("examples/" + match[1] + ".rplpp").done(setEditorContent);
      return;
    }

    match = hash.match(/#([a-z0-9]{8})/);
    if (match) {
      $.get("load.php", {hash: match[1]}).done(setEditorContent);
    }
  }

  function getOptions() {
    var options = {
      intSize: $("#options input[name='options-int-size']:checked").val()
    };
    return options;
  }

  var spinnerTimeout;
  function execute(options) {
    defaults = {
      "outputHeight": 200,
      "invert": false
    }
    if (typeof options == "object") {
      options = $.extend(defaults, options);
    } else {
      options = defaults;
    }
    showOutputPane(options.outputHeight);
    spinnerTimeout = window.setTimeout(function() { $executing.fadeIn(); }, 1000);

    var code = editor.getValue();
    $.post("execute.php", {
      "code": code,
      "invert": options.invert ? "on" : "off"
    })
    .done(formatOutput)
    .fail(formatError)
    .always(function() {
      window.clearTimeout(spinnerTimeout);
      $executing.fadeOut();
    });
  }

  function compile(options) {
    defaults = {
      "outputHeight": 200,
      "compile": true
    }
    if (typeof options == "object") {
      options = $.extend(defaults, options);
    } else {
      options = defaults;
    }
    showOutputPane(options.outputHeight);
    spinnerTimeout = window.setTimeout(function() { $executing.fadeIn(); }, 1000);

    var code = editor.getValue();
    $.post("execute.php", {
      "code": code,
      "compile": options.compile ? "on" : "off"
    })
    .done(initDownloading)
    .fail(formatError)
    .always(function() {
      window.clearTimeout(spinnerTimeout);
      $executing.fadeOut();
    });
  }

  var prevErrors = [];
  function removeErrorMarkers() {
    var session = editor.getSession();
    for (var i = 0; i < prevErrors.length; ++i) {
      session.removeGutterDecoration(prevErrors[i], "errorGutter");
      prevErrors = [];
    }
  }

  function showOutputPane(newHeight) {
    newHeight = newHeight || 160;
    $outputPane.animate({
      height: newHeight
    }, {
      duration: 200,
      done: function() {
        $editor.css("bottom", $outputPane.outerHeight()+"px");
        editor.resize();
      }
    });
  }

  function hideOutputPane() {
    $editor.css("bottom", "0");
    editor.resize();
    $outputPane.animate({
      height: 0
    }, {
      duration: 200
    });
  }

  function formatOutput(output) {
    // First line contains the exit code
    var retval = parseInt(output.substr(0, output.indexOf("\n")));
    output = output.substring(output.indexOf("\n") + 1);

    removeErrorMarkers();
    if (retval > 0) {
      var session = editor.getSession();
      var match = output.match(/line (\d+), column (\d+)/);

      if (match) {
        var line = parseInt(match[1]) - 1;
        session.addGutterDecoration(line, "errorGutter");
        prevErrors.push(line);
      }
      $output.html($("<pre>").text(output).addClass("error"));
    } else {
      $output.html($("<pre>").text(output));
    }
  }

  function formatError(data) {
    $output.html(
      '<div class="alert alert-error">An error occured while trying to run the program.</div>'
    );
  }

  function initDownloading(output) {
    // First line contains the exit code
    var retval = parseInt(output.substr(0, output.indexOf("\n")));
    output = output.substring(output.indexOf("\n") + 1);

    removeErrorMarkers();
    if (retval > 0) {
      var session = editor.getSession();
      var match = output.match(/line (\d+), column (\d+)/);

      if (match) {
        var line = parseInt(match[1]) - 1;
        session.addGutterDecoration(line, "errorGutter");
        prevErrors.push(line);
      }
      $output.html($("<pre>").text(output).addClass("error"));
    } else {
      startDownload("program.pal", output);
    }
  }

  // https://stackoverflow.com/a/18197341
  function startDownload(filename, content) {
    var element = document.createElement('a');
    element.setAttribute('href', 'data:text/roopl;charset=utf-8,' + encodeURIComponent(content));
    element.setAttribute('download', filename);

    element.style.display = 'none';
    document.body.appendChild(element);

    element.click();

    document.body.removeChild(element);
  }

  $("#examples a").click(function(e) {
    loadCode(e.target.hash);
  });

  $("#run").click(execute);

  $("#invert").click(function() {
    execute({outputHeight: 400, invert: true});
  });

  $("#compile").click(function() {
    compile({outerHeight: 400, compile: true});
  })

  $("#output-pane button.close").click(hideOutputPane);

  var sharePopoverVisible = false;
  $("#share").click(function(e) {
    var code = editor.getValue();
    $.post("save.php", {"code": editor.getValue()})
    .done(function(res) {
      var url = location.protocol+'//'+location.host+location.pathname+"#"+res;
      $("#share").popover({
        title: "Share this URL",
        content: "<input value=\""+url+"\" type=text size=40>",
        placement: "bottom",
        html: true,
        trigger: "manual"
      }).popover("show");
      // Select input field in popover
      $(".popover input").select();
      // Prevent click event from bubbling up to document.
      $(".popover").bind("click", function(e) { return false; });
      sharePopoverVisible = true;
    });
    return false;
  });

  $(document).click(function() {
    if (sharePopoverVisible) {
      $("#share").popover("destroy");
    }
  });

  $(window).on("hashchange", function() { loadCode(location.hash); });
  $(window).on("beforeunload", function() {
    return "All your changes will be lost when you leave the site.";
  });

  loadCode(location.hash);
});
