import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;

import util.ToolIO;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

/**
 * Dumps SANY's own verdict for a TLA+ file, as machine-readable lines:
 *
 * <pre>
 *   #FILE &lt;path&gt;
 *   &lt;definition name&gt;\t&lt;level&gt;
 *   ...
 *   #PARSE_ERR   &lt;path&gt;\t&lt;reason&gt;   -- SANY could not parse it
 *   #RESOLVE_ERR &lt;path&gt;\t&lt;reason&gt;   -- parsed, but an EXTENDS was missing
 * </pre>
 *
 * Levels are SANY's: 0 constant, 1 state, 2 action, 3 temporal. Only
 * definitions originating in the root module are printed; anything pulled in
 * through EXTENDS belongs to another module.
 *
 * This is a TEST ORACLE only — the same relationship {@code bench/z3_parity}
 * has with Z3. Nothing Nixie ships depends on a JVM; SANY is consulted to
 * check the pure-Rust front end against, never linked.
 */
public class LevelDump {
    private static String trim(String s) {
        return s.length() > 200 ? s.substring(0, 200) : s;
    }

    public static void main(String[] args) {
        // Buffer SANY's narration instead of printing it.
        ToolIO.setMode(ToolIO.TOOL);
        for (String file : args) {
            try {
                SpecObj spec = new SpecObj(file, null);
                // SANY narrates to System.out as well as to the stream it is
                // handed, so both have to be muzzled for the output to stay
                // machine-readable.
                PrintStream sink = new PrintStream(new ByteArrayOutputStream());
                PrintStream realOut = System.out;
                ModuleNode root;
                try {
                    System.setOut(sink);
                    SANY.frontEndMain(spec, file, sink);
                    root = spec.getExternalModuleTable().getRootModule();
                } finally {
                    System.setOut(realOut);
                }
                if (root == null) {
                    // Distinguish "SANY could not parse this file" from "SANY
                    // parsed it but could not resolve an EXTENDS". Only the
                    // first is a syntax verdict; the second still means the
                    // file's own syntax was fine.
                    String all = String.join(" | ", ToolIO.getAllMessages()).replace('\n', ' ');
                    // The API surfaces a syntax failure as "***Parse Error***";
                    // the CLI phrases the same thing as "Could not parse
                    // module". Accept either, or a resolution failure is
                    // reported where a syntax failure happened -- which shows
                    // up downstream as a phantom parity gap.
                    String tag = (all.contains("Could not parse module")
                            || all.contains("***Parse Error***"))
                            ? "#PARSE_ERR"
                            : "#RESOLVE_ERR";
                    System.out.println(tag + "\t" + file + "\t" + trim(all));
                    ToolIO.reset();
                    continue;
                }
                ToolIO.reset();
                String rootName = root.getName().toString();
                System.out.println("#FILE\t" + file);
                for (OpDefNode d : root.getOpDefs()) {
                    ModuleNode origin = d.getOriginallyDefinedInModuleNode();
                    if (origin == null || !origin.getName().toString().equals(rootName)) {
                        continue;
                    }
                    System.out.println(d.getName() + "\t" + d.getLevel());
                }
            } catch (Throwable t) {
                System.out.println("#RESOLVE_ERR\t" + file + "\t" + t.getClass().getSimpleName());
            }
        }
    }
}
