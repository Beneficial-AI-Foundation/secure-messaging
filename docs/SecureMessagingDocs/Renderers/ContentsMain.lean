import SecureMessagingDocs.Render
import SecureMessagingDocs.Contents

def main (args : List String) : IO UInt32 :=
  SecureMessagingDocs.renderManual (%doc SecureMessagingDocs.Contents) args
