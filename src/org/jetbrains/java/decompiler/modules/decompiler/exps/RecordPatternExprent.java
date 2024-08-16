package org.jetbrains.java.decompiler.modules.decompiler.exps;

import org.jetbrains.java.decompiler.util.TextBuffer;

import java.util.BitSet;
import java.util.List;
import java.util.stream.Stream;

public class RecordPatternExprent extends Exprent implements PatternExprent {

  private ConstExprent recordType;
  private List<Exprent> fields;

  public RecordPatternExprent(ConstExprent recordType, List<Exprent> fields, BitSet bytecodeOffsets) {
    super(Type.RECORD_PATTERN);
    this.recordType = recordType;
    this.fields = fields;

    addBytecodeOffsets(bytecodeOffsets);
  }

  @Override
  protected List<Exprent> getAllExprents(List<Exprent> list) {
    list.add(recordType);
    list.addAll(fields);
    return list;
  }

  @Override
  public Exprent copy() {
    return new RecordPatternExprent(recordType, fields, bytecode);
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer text = new TextBuffer();
    text.append(recordType.toJava(indent));
    TextBuffer fieldsText = new TextBuffer();
    fieldsText.pushNewlineGroup(indent, 1);
    fieldsText.appendPossibleNewline();
    fieldsText.pushNewlineGroup(indent, 0);
    for (int i = 0; i < fields.size(); i++) {
      if (i != 0) {
        fieldsText.append(",");
        fieldsText.appendPossibleNewline(" ");
      }
      Exprent field = fields.get(i);
      fieldsText.append(field.toJava(indent));
    }
    fieldsText.popNewlineGroup();
    fieldsText.appendPossibleNewline("", true);
    fieldsText.popNewlineGroup();
    text.append(fieldsText.encloseWithParens());
    return text;
  }

  @Override
  public void getBytecodeRange(BitSet values) {
    measureBytecode(values, recordType);
    measureBytecode(values, fields);
    measureBytecode(values);
  }

  @Override
  public List<PatternExprent> getChildExprents() {
    return fields.stream().map(exp -> (PatternExprent) exp).toList();
  }

}
