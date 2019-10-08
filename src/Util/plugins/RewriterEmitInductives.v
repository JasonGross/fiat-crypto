Require Import Crypto.Language.Pre.

Register ScrapedData.t as rewriter.scraped_data.type.
Register GallinaIdentList.t as rewriter.pair_list.type.
Register GallinaIdentList.nil as rewriter.pair_list.nil.
Register GallinaIdentList.cons as rewriter.pair_list.cons.
Register Named.t as rewriter.named.type.
Register Named.maybe_name as rewriter.maybe_name.type.
Register Named.a_name as rewriter.maybe_name.a_name.
Register Named.no_name as rewriter.maybe_name.no_name.

Declare ML Module "rewriter_emit_inductives_plugin".

Require Import Crypto.Language.IdentifierParameters.


Rewriter Emit Inductives From
        {| ScrapedData.base_type_list_named := base_type_list_named ; ScrapedData.all_ident_named_interped := all_ident_named_interped |}
        As base ident raw_ident pattern_ident.
