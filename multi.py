#!/usr/bin/env python3.3

import fileinput
import os
import signal
import subprocess
import time
import sys
from threading import Thread

class Reader(Thread):
    def __init__(self, input):
        Thread.__init__(self)
        self.input = input
        self.under = []
        self.over = []
        self.active = False
        self.incoherent = False
        self.verbatim = []

    def run(self):
        self.active = True
        while self.active:
            line = self.input.readline().decode()
            if not line:
                self.active = False
            elif line[0] == 'c':
                self.under.extend(line.split()[1:])
            elif line[0] == 'r':
                self.over.extend(line.split()[1:])
            elif line[0] in ['b', 'u']:
                self.verbatim.append(line)
            elif line[0] == 'I':
                self.incoherent = True
                self.active = False
            else:
                pass
            
    def stop(self):
        self.active = False
        
    def getUnder(self):
        (res, self.under) = (self.under, [])
        return res

    def getOver(self):
        (res, self.over) = (self.over, [])
        return res
        
    def getVerbatim(self):
        (res, self.verbatim) = (self.verbatim, [])
        return res

class Process(Thread):
    def __init__(self, id, args):
        Thread.__init__(self)
        
        self.id = id
        self.process = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=None)
        self.reader = Reader(self.process.stdout)
        
        self.idToName = {}
        self.under = {}
        self.over = {}
        
        if id == 1:
            self.sound = []
            self.removed = []
            self.soundIndex = 0
            self.removedIndex = 0
        
        self.addUnder = []
        self.addUnderIndex = 0
        self.removeOver = []
        self.removeOverIndex = 0
        
        self.addVerbatim = []
        self.addVerbatimIndex = 0
        
    def run(self):
        #self.process.stdin.close()
        self.flush()
        
        # after simplifications
        names = self.readline().decode().strip().split()[1:]
        under = self.readline().decode().strip().split()[1:]
        over = self.readline().decode().strip().split()[1:]
        for i in range(0, len(under)):
            self.idToName[under[i]] = names[i]
        for i in range(0, len(over)):
            self.idToName[over[i]] = names[len(under) + i]
        self.under = dict.fromkeys(under)
        self.over = dict.fromkeys(over)
            
        if self.id == 1:
            self.printCertain()
            self.printPossible()
            self.sound = [a for a in self.under]
            self.soundIndex = len(self.sound)
            

        self.reader.start()

        while self.over:
            #print("AAAA %d" % len(over))
            time.sleep(0.01)
            

            if self.id == 1:
                if self.other.reader.incoherent:
                    print("INCHOERENT")
                    self.reader.stop()
                    return
                if self.soundIndex < len(self.sound):
                    self.printSound()
                if self.removedIndex < len(self.removed):
                    self.printRemoved()
            elif self.id == 2:
                if self.reader.incoherent:
                    self.reader.stop()
                    return
            
            while self.addUnderIndex < len(self.addUnder):
                a = self.addUnder[self.addUnderIndex]
                if a not in self.under:
                    self.under[a] = True
                    del self.over[a]
                    self.write(("a %s\n" % a).encode())
                    self.flush()
                    if self.id == 1:
                        self.sound.append(a)
                self.addUnderIndex = self.addUnderIndex + 1
            
            while self.removeOverIndex < len(self.removeOver):
                a = self.removeOver[self.removeOverIndex]
                if a in self.over:
                    del self.over[a]
                    self.write(("r %s\n" % a).encode())
                    self.flush()
                    if self.id == 1:
                        self.removed.append(a)
                self.removeOverIndex = self.removeOverIndex + 1

            self.other.addVerbatim.extend(self.reader.getVerbatim())
            while self.addVerbatimIndex < len(self.addVerbatim):
                #print("verb %s" % self.addVerbatim[self.addVerbatimIndex])
                self.write(self.addVerbatim[self.addVerbatimIndex].encode())
                self.flush()
                self.addVerbatimIndex = self.addVerbatimIndex + 1
            
            atoms = self.reader.getUnder()
            for a in atoms:
                if a not in self.under:
                    self.under[a] = True
                    del self.over[a]
                    #print(("a %s" % a))
                    if a not in self.other.under:
                        self.other.addUnder.append(a)
                    if self.id == 1:
                        self.sound.append(a)

            atoms = self.reader.getOver()
            for a in atoms:
                if a in self.over:
                    del self.over[a]
                    #print("r %s" % a)
                    if a in self.other.over:
                        self.other.removeOver.append(a)
                    if self.id == 1:
                        self.removed.append(a)

        self.reader.stop()
        
        if self.id == 1:
            #print("Cautious consequences:")
            #print(" ".join(self.under))
            self.printPossibleFinal()
            self.printCertain()
        #print("%d DONE" % self.id, file=sys.stderr)
        
    def write(self, line):
        try:
            self.process.stdin.write(line)
        except:
            pass
    
    def flush(self):
        try:
            self.process.stdin.flush()
        except:
            pass
        
    def readline(self):
        return self.process.stdout.readline()

    def printSound(self):
        global begin
        print("[%dms] Certain answers (%d):" % ((time.time() - begin) * 1000, len(self.under)))
        print(" ".join([self.idToName[a] for a in self.sound[self.soundIndex:]]))
        self.soundIndex = len(self.sound)

    def printRemoved(self):
        global begin
        print("[%dms] Possible answers (%d; %d). Candidates removed (%d):" % ((time.time() - begin) * 1000, len(self.under) + len(self.over), len(self.over), len(self.removed) - self.removedIndex))
        print(" ".join([self.idToName[a] for a in self.removed[self.removedIndex:]]))
        self.removedIndex = len(self.removed)

    def printCertain(self):
        global begin
        if self.id == 1:
            print("[%dms] Certain answers (%d):" % ((time.time() - begin) * 1000, len(self.under)))
            print(" ".join([self.idToName[a] for a in self.under]))

    def printPossible(self):
        global begin
        if self.id == 1:
            print("[%dms] Possible answers (%d; %d):" % ((time.time() - begin) * 1000, len(self.under) + len(self.over), len(self.over)))
            print(" ".join([self.idToName[a] for a in self.over]))

    def printPossibleFinal(self):
        global begin
        if self.id == 1:
            print("[%dms] Possible answers (%d; 0):" % ((time.time() - begin) * 1000, len(self.under)))
            #print(" ".join([self.idToName[a] for a in self.over]))
        

if __name__ == "__main__":
    wasp = sys.argv[1] if len(sys.argv) == 2 else "wasp"

    begin = time.time()

    process1 = Process(1, [wasp, "--query=5", "--multi"])
    process2 = Process(2, [wasp, "--query=2", "--multi"])
    process1.other = process2
    process2.other = process1

    for line in fileinput.input("-"):
        line = line.encode()
        process1.write(line)
        process2.write(line)

    process1.start()
    process2.start()
    
