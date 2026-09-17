FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

# Source ranges appear in the exported JSON and in the warning about an
# unusable payload, so keep absolute paths out of the expected outputs.
OTHERFLAGS += --ext fstar:no_absolute_paths

DOCS_HTML := python3 $(FSTAR_ROOT)/.scripts/fstardoc/docs_json_to_html.py
IDE_CLEANUP := python3 ../ide/cleanup.py

# The versioned JSON documentation index of a module, read out of its
# checked file. --export_docs prefers the interface's checked file when
# there is one, which is what the extra prerequisite below guarantees is
# available for DocsFixture.
$(OUTPUT_DIR)/%.docs.json: $(CACHE_DIR)/%.fst.checked
	$(call msg, "EXPORT_DOCS", $(basename $(notdir $<)))
	$(FSTAR) --export_docs $< > $@

$(OUTPUT_DIR)/DocsFixture.docs.json: $(CACHE_DIR)/DocsFixture.fsti.checked

# Copy the implementation cache to a name that does not end in .fst.checked.
# This bypasses sibling-interface discovery. Since the cache records that an
# interface was used, export must fail rather than guess at the public surface.
$(OUTPUT_DIR)/DocsFixture.impl-copy.checked: $(CACHE_DIR)/DocsFixture.fst.checked
	$(call msg, "COPY_CHECKED", $(basename $(notdir $<)))
	cp $< $@

$(OUTPUT_DIR)/DocsFixture.from-copy.docs.stderr: $(OUTPUT_DIR)/DocsFixture.impl-copy.checked
	$(call msg, "EXPORT_DOCS_ERR", $(basename $(notdir $<)))
	-$(FSTAR) --export_docs $< 2> $@.raw > /dev/null
	awk 'NF { last=NR } { line[NR]=$$0 } END { for (i=1; i<=last; i++) print line[i] }' $@.raw > $@
	rm $@.raw

# A stale sibling interface must not override an implementation that records
# no interface. Use output-directory copies so the real caches stay untouched.
$(OUTPUT_DIR)/DocsNoIface.fst.checked: $(CACHE_DIR)/DocsNoIface.fst.checked
	cp $< $@

$(OUTPUT_DIR)/DocsNoIface.fsti.checked: $(CACHE_DIR)/DocsFixture.fsti.checked
	cp $< $@

$(OUTPUT_DIR)/DocsNoIface.with-stale-interface.docs.json: \
  $(OUTPUT_DIR)/DocsNoIface.fst.checked \
  $(OUTPUT_DIR)/DocsNoIface.fsti.checked
	$(call msg, "EXPORT_DOCS", $(basename $(notdir $<)))
	$(FSTAR) --export_docs $(OUTPUT_DIR)/DocsNoIface.fst.checked > $@

# Diagnostics from the same export, on stderr, kept apart from the JSON
# so that the JSON stays machine-readable.
$(OUTPUT_DIR)/%.docs.stderr: $(CACHE_DIR)/%.fst.checked
	$(call msg, "EXPORT_DOCS_ERR", $(basename $(notdir $<)))
	$(FSTAR) --export_docs $< 2> $@ > /dev/null

# The static HTML page, rendered from the JSON alone.
$(OUTPUT_DIR)/%.docs.html: $(OUTPUT_DIR)/%.docs.json
	$(call msg, "DOCS_HTML", $(basename $(notdir $<)))
	$(DOCS_HTML) $< > $@

# An interactive session looking documented and undocumented names up.
# The fixtures must already be checked when the session starts, or the
# first response would carry warnings about unchecked dependencies.
$(OUTPUT_DIR)/%.ideout: %.in $(ALL_CHECKED_FILES)
	$(call msg, "OUT_IDE", $<)
	$(eval FST := $(firstword $(subst ., ,$<)))
	$(FSTAR) --ide --silent "$(realpath ${FST}.fst)" < "$<" | $(IDE_CLEANUP) "$@"
