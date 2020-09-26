#!/usr/bin/env ruby
#
require (ENV['FGPREFIX'] + '/Tools/StagesScripts/globals')
require 'set'
#require 'bigdecimal'
#require "bigdecimal/math.rb"
#include BigMath
#def logsumexp( values )
#  BigMath.log((values.map {|v| v - values.max}).inject(0) {|acc,val| acc + BigMath.exp(val, 10)}, 10) + values.max
#end

def average_outputs( input_dir, simulation, num_to_use )
  $stderr.puts "Averaging grammar files for #{simulation.inspect}"
  scores = {}
  $grammars = {}
 
  pattern = "#{input_dir}/#{STAGES_DIR}/#{simulation[:Name].join('-')}.#{FG_OUTPUT_INFIX}-[0-9]*.rank-[0-9]*.txt"
  #pattern = "#{input_dir}/#{STAGES_DIR}/#{simulation[:Name].join('-')}.num-[0-9]*.#{FG_OUTPUT_INFIX}-[0-9]*.rank-[0-9]*.txt"
  $stderr.puts "Pattern: #{pattern}\n" # Thang
  files = Dir.glob(pattern)
  $stderr.puts "\tFound #{files.length} grammar files!"
 
  scores = Array.new(files.length,LOG0)
  num_to_use = files.length if num_to_use == -1 or num_to_use > files.length
  $stderr.puts "\tUsing #{num_to_use} grammar files!"

  number = 0
  good=0
  bad=0
  files.each do |file|
    $stderr.puts "Getting Score for file number #{number}: #{file}"    
    f=File.new(file,'r')    
    line = f.gets
    /# (.+)/ =~ line
    score_string=$1
    #puts score_string
    if /(^-?[e\-0-9.]+?)/ =~ score_string and score_string.to_f < 0.0
      score = score_string.to_f
      scores[number] =  [score,file] 
      # $stderr.puts "\tScore #{score}"
      f.close
      good += 1
    else
      scores[number] =  [LOG0,file] 
      # $stderr.puts "\tBad Score: #{file}, #{score_string}, #{line}"
      bad += 1
    end
    number += 1
  end

  $stderr.puts "\tGood file: #{good}, Bad files: #{bad}"

  ss = scores.sort {|a,b| b.first <=> a.first}
  sorted_scores = ss.slice(0,num_to_use)
  normalizer = logsumexp(sorted_scores.map {|v| v.first})
  $stderr.puts "\tNormalizer: #{normalizer}, Best: #{ss.first.first}, Normalizer-Best: #{normalizer - ss.first.first }"
  normalized_scores = sorted_scores.map {|v| v.first - normalizer}
  #ss.each do |score, file|
  #  puts "#{score}, #{score-normalizer},  #{Math.exp(score-normalizer)}, #{score - ss.first.first}, #{Math.exp(score - ss.first.first)}, #{file}"
  #end 

  number=0
  all_rules = Hash.new LOG0
  total = []
  sorted_scores.each do |score,file|
    if not score == LOG0
      $stderr.puts "Found FG run output file number #{number}: #{file} of #{sorted_scores.length}"
      
      normalized_grammar_score = normalized_scores[number]
      
      new_rules = 0
      f=File.open(file)
      lines = f.readlines
      f.close
      if lines.length > 0
        lines.each do |line|
          #$stderr.puts "#{line}\n" # Thang
          if /(^-?[e\-0-9.]+?) (.+)/ =~ line.strip then
            rule_weight = $1.to_f; rule = $2.strip
            rule_weight = 0.0 if rule_weight > 0.0
            if not all_rules.include? rule
              new_rules += 1 
              all_rules[rule] =  (rule_weight + normalized_grammar_score)
            else
              all_rules[rule] = logsumexp([all_rules[rule],  (rule_weight + normalized_grammar_score)])
            end
          end
        end
        number += 1
        # $stderr.puts "\tFound #{new_rules} new rules for a total of #{all_rules.size}."
      end
    end
  end

  $stderr.puts "\tFound #{number} grammars"

  File.delete "#{input_dir}/#{STAGES_DIR}/#{simulation[:Name].join('-')}.#{POSTERIOR_ESTIMATE_INFIX}.txt" if File.exists? "#{input_dir}/#{STAGES_DIR}/#{simulation[:Name].join('-')}.#{POSTERIOR_ESTIMATE_INFIX}.txt"
  posterior_estimate_file =  File.open("#{input_dir}/#{STAGES_DIR}/#{simulation[:Name].join('-')}.#{POSTERIOR_ESTIMATE_INFIX}.txt",'w')
  posterior_estimate_file.puts normalizer.to_s
  posterior_estimate_file.close

  corrected_rules = Hash.new LOG0
  all_rules.each_pair do |rule,weight|
    #$stderr.puts "#{rule}\t#{weight}\t#{corrected_rules[new_rule]}\n"
    new_rule=rule #rule.gsub(/(BNd|BNT)/,"BND")
    corrected_rules[new_rule]=logsumexp([corrected_rules[new_rule],weight])
  end

  $stderr.puts "Printing Averaged Grammar"
  File.delete "#{input_dir}/#{STAGES_DIR}/#{simulation[:Name].join('-')}.FG-#{GRAM_INFIX}.txt" if File.exists? "#{input_dir}/#{STAGES_DIR}/#{simulation[:Name].join('-')}.FG-#{GRAM_INFIX}.txt"
  output_file = File.open("#{input_dir}/#{STAGES_DIR}/#{simulation[:Name].join('-')}.FG-#{GRAM_INFIX}.txt",'w')
  corrected_rules.each_pair do |rule,weight|
    output_file.puts "#{weight.to_s} #{rule}"
  end
  output_file.close
end

input_dir = ARGV[0]
simulations = find_inputs( input_dir )

num_to_use = -1
num_to_use =  ARGV[1] if ARGV[1]

simulations.each_value do |sim|
  average_outputs( input_dir, sim,  num_to_use.to_i)
end
