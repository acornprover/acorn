<script context="module">
  let vscode = acquireVsCodeApi();
</script>

<script lang="ts">
  import { onMount } from "svelte";
  import Citation from "./Citation.svelte";
  import Selection from "./Selection.svelte";

  // These are updated to reflect the last valid responses from the extension.
  let selectionResponse: SelectionResponse | null = null;
  let help: Help | null = null;

  function handleSelectionResponse(response: SelectionResponse) {
    if (response.failure || (response.goals.length === 0 && response.citation === null)) {
      // Failure responses should not reach this point.
      console.error("unexpected upstream failure:", response.failure);
      return;
    }

    selectionResponse = response;
  }

  onMount(() => {
    window.addEventListener("message", (event) => {
      if (event.data.type === "selection") {
        handleSelectionResponse(event.data.response);
        return;
      }
      if (event.data.type === "help") {
        help = event.data.help;
        return;
      }
      console.error("unexpected message type:", event.data.type);
    });
  });

  function showLocation(uri: string, range: Range) {
    vscode.postMessage({ command: "showLocation", uri, range });
  }
</script>

<main>
  {#if selectionResponse !== null && (selectionResponse.goals.length > 0 || selectionResponse.citation !== null)}
    {#if selectionResponse.citation !== null}
      <Citation
        citation={selectionResponse.citation}
        uri={selectionResponse.uri}
        {showLocation}
      />
    {:else}
      <Selection {selectionResponse} {showLocation} />
    {/if}
  {:else}
    {#if help !== null && help.noSelection}
      Select a proposition to see its proof.
    {:else if help !== null && help.newDocument}
      Enter a theorem that you want to prove.
      <br /><br />
      When you're ready, save the file to verify it.
    {:else}
      <!-- Default message to be shown when we don't even have an Acorn file open. -->
      This is the Acorn Assistant.
      <br /><br />
      To get started, open an Acorn file, or create a new one.
      <br /><br />
      An Acorn file has to have a .ac extension.
    {/if}
    <br /><br />
    For help, see the
    <a href="https://acornprover.org">documentation</a>.
  {/if}
</main>
