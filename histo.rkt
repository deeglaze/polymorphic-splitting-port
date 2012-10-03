#lang racket

(provide make-histogram)

; Put up a histogram.
; Title is the window title (a string).
; Counts is a list of the histogram counts.
; The graph is scaled so that it shows counts between 0 and max-count.
; Negative counts are shown in blue, positive counts in red.
(define make-histogram
  (lambda (title max-count counts)
    (unless (string? title)
      (error 'make-histogram "Bad title: ~s" title))
    (unless (and (number? max-count)
                 (real? max-count)
                 (> max-count 0))
      (error 'make-histogram "Bad max-count: ~s" max-count))
    (unless (list? counts)
      (error 'make-histogram "Counts is not a proper list: ~s" counts))
    (for-each
      (lambda (c)
        (unless (and (number? c) (real? c))
          (error 'make-histogram "Bad count: ~s" c)))
      counts)
    (let* ([in.out.pid (process "exec wish")]
           [out (cadr in.out.pid)]
           [send (lambda (fmt . args) (apply fprintf out fmt args))])      
      (close-input-port (car in.out.pid))
      (parameterize ([current-output-port out])
        (printf "wm title . \"")
        (for-each
         (lambda (ch)
           (printf "~a"
                   (case ch
                     ((#\$)
                      "\\$")
                     ((#\")
                      "\\\"")
                     (else
                      ch))))
         (string->list title))
        (printf "\"~%")
        (for-each
         (lambda (cmd)
           (printf "~a~%" cmd))
         '("canvas .canvas -width 750 -height 250"
           "pack .canvas -expand yes -fill both"
           "wm minsize . 10 10"
           "proc resize {width height} {"
           "        global bins max size"
           ""
           "        set bwidth [expr ($width + 0.0) / $size]"
           "        set hscale [expr ($height + 0.0) / $max]"
           "        set x 0"
           "        set i 1"
           "        foreach bin $bins {"
           "                set xhigh [expr $x + $bwidth]"
           "                if {$bin < 0} {"
           "                        set y $height"
           "                } elseif {$bin > $max} {"
           "                        set y 0"
           "                } else {"
           "                        set y [expr $height - $bin * $hscale]"
           "                }"
           "                .canvas coords $i $x $height $xhigh $y"
           "                set x $xhigh"
           "                incr i"
           "        }"
           "}"))
        (printf "set bins {")
        (for-each
         (lambda (h)
           (printf "        ~a~%" (abs h)))
         counts)
        (printf "}~%")
        (for-each
         (lambda (h)
           (if (negative? h)
               (printf "~a~%"
                       ".canvas create rectangle 0 0 0 0 -fill blue -outline {}")
               (printf "~a~%"
                       ".canvas create rectangle 0 0 0 0 -fill red -outline {}")))
         counts)
        (printf "set max ~a~%" max-count)
        (printf "set size ~a~%" (length counts))
        (printf "resize 100 100~%")
        (printf "~a~%"
                "bind . <Configure> {resize %w %h}"))
      (close-output-port out))))
