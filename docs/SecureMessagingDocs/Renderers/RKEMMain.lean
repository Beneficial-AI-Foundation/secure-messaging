import SecureMessagingDocs.Render
import SecureMessagingDocs.Chapters.RKEM.Overview

def main (args : List String) : IO UInt32 :=
  SecureMessagingDocs.renderManual (%doc SecureMessagingDocs.Chapters.RKEM.Overview) args