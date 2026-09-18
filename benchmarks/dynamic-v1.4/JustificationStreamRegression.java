import java.io.*;
import com.fasterxml.jackson.databind.*;
public class JustificationStreamRegression {
 static class Producer extends InputStream {
  final byte[] first = "{\"status\":\"ok\"}".getBytes(); int pos=0; boolean closed=false, drained=false;
  public int read() throws IOException {
   if(closed) throw new IOException("producer pipe prematurely closed");
   if(pos<first.length)return first[pos++];
   if(pos++==first.length)return '\n';
   drained=true;return -1;
  }
  public int read(byte[] b,int off,int len)throws IOException {
   if(pos>=first.length)return super.read(b,off,len);
   int n=Math.min(len,first.length-pos);System.arraycopy(first,pos,b,off,n);pos+=n;return n;
  }
  public void close(){closed=true;}
 }
 public static void main(String[] args)throws Exception {
  ObjectMapper mapper=new ObjectMapper();Producer old=new Producer();mapper.readTree(old);
  if(!old.closed || old.drained)throw new AssertionError("did not reproduce early close");
  Producer fixed=new Producer();JsonNode r=mapper.readTree(fixed.readAllBytes());
  if(!fixed.drained||!r.path("status").asText().equals("ok"))throw new AssertionError("drain failed");
  System.out.println("PASS: pinned runtime closes live stream before EOF; draining first preserves response and consumes trailing newline.");
 }
}
