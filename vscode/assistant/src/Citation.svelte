<script lang="ts">
  export let citation: CitationInfo;
  export let uri: string;
  export let showLocation: (uri: string, range: Range) => void;

  function showSelection() {
    showLocation(uri, citation.range);
  }
</script>

<span class="header goal-link" on:click={showSelection}
  >{citation.selectionText}</span
>
<hr />
<br />

<div class="block">
  {#if citation.theoremName !== null}
    Citation of
    {#if citation.theoremLocation !== null}
      <span
        class="preview-link"
        on:click={() => {
          if (citation.theoremLocation !== null) {
            showLocation(citation.theoremLocation.uri, citation.theoremLocation.range);
          }
        }}>{citation.theoremName}</span
      >
    {:else}
      <span>{citation.theoremName}</span>
    {/if}
    expands to:
  {:else}
    Citation expands to:
  {/if}
  <br /><br />
  <div class="code-block">{citation.expansion}</div>
</div>

<style>
  .goal-link {
    cursor: pointer;
  }

  .goal-link:hover {
    text-decoration: underline;
  }

  .preview-link {
    cursor: pointer;
    color: var(--vscode-textLink-foreground);
  }

  .preview-link:hover {
    text-decoration: underline;
  }

  .code-block {
    white-space: pre-wrap;
    font-family: monospace;
  }
</style>
