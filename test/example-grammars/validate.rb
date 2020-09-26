require 'bigdecimal'
require "bigdecimal/math"

include BigMath

def get_sums(file)
  f=File.open(file, 'r')
  scores=Hash.new {|k,v| k[v] = []}
  f.each_line do |line|
    next if line =~ /^#/
    parts=line.strip.split
    score=BigDecimal(parts[0].strip)
    lhs=parts[1].strip
    scores[lhs]=scores[lhs] << score
  end
  
  $out = File.open("debug.txt", 'w')
  scores.each_pair do |lhs,ps|
    $out.puts("c(#{(ps.map {|x| x.to_f.to_s}).join(",")})")
    max=ps.inject(BigDecimal("0")) { |result, element| if element > result then element else result end}
    ps2 = ps.map {|elem| elem - max}
    total = ps2.inject(BigDecimal("0")) {|res,elem| res + exp(elem,10)}
    logprob=log(total,10)+max
    final=exp(logprob,10)
    dif = (BigDecimal("1.0") - final).abs
    if not(dif.round(5) == 0.0)
      puts "#{lhs} #{dif.round(5)}"
    end
  end

end
puts "FG\n"
get_sums("FG.txt")
puts "AG\n"
get_sums("AG.txt")
puts "MDPCFG\n"
get_sums("MDPCFG.txt")
puts "DOP1\n"
get_sums("DOP1.txt")
puts "GDMN\n"
get_sums("GDMN.txt")





