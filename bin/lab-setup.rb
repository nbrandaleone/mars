#! /usr/bin/env ruby

# Create or update the user's .irbrc file.  Set the prompt to the simple prompt
# shown in the textbook, but if there is already a prompt setting don't change it.
# Add lines to require rubygems and rubylabs on each new IRB session.

def configure
  Dir.chdir do
    irbrc = File.exist?(".irbrc") ? File.open(".irbrc").readlines : []
    newlines = []
    if irbrc.grep(/PROMPT_MODE/).empty?
      newlines << "IRB.conf[:PROMPT_MODE] = :SIMPLE"
    end
    ['rubygems','rubylabs'].each do |file|
      if irbrc.grep(/require '#{file}'/).empty?
        newlines << "require '#{file}'"
      end
    end
    if newlines.empty?
      puts ".irbrc already initialized -- no changes made"
    else
      puts "adding lines to .irbrc:"
      File.open(".irbrc", "a") do |f|
        f.puts "# lines added by RubyLabs installer script"
        newlines.each do |line|
          f.puts line
          puts "  " + line
        end
      end
    end
  end
  puts "** .irbrc configuration: OK\n"
end

if !defined? IRB
  configure
end
