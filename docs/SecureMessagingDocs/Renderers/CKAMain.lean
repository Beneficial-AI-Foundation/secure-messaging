import SecureMessagingDocs.Render
import SecureMessagingDocs.Chapters.CKA.Overview

def main (args : List String) : IO UInt32 :=
  SecureMessagingDocs.renderManual (%doc SecureMessagingDocs.Chapters.CKA.Overview) args