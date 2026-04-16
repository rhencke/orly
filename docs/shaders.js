// ── Q3 shader script parser and loader ──────────────────────────────
//
// Minimal Q3 shader script parser that extracts texture map directives.
// Q3 shaders map texture names (from the BSP) to diffuse texture images
// and material properties.  This module parses shader files and builds a
// lookup table: texture_name → diffuse image path.
//
// Q3 shader format (simplified for this viewer):
//   textures/base_wall/concrete_wall
//   {
//     map $lightmap
//     map textures/base_wall/concrete_wall.jpg
//   }
//
// We extract the "map" directives after "$lightmap" to find the diffuse.

/**
 * Parse a single Q3 shader script string and return a Map of
 * shader_name → { diffuseMap: "path/to/texture.jpg" }.
 *
 * Handles multi-line shader blocks and extracts texture map directives.
 */
export function parseShaderScript(scriptText) {
  const shaders = new Map();

  // Tokenize: braces, identifiers, quoted strings
  const tokens = [];
  const re = /\{|\}|"[^"]*"|[^\s\{\}]+/g;
  let m;
  while ((m = re.exec(scriptText)) !== null) {
    const tok = m[0];
    if (tok === '{' || tok === '}') {
      tokens.push({ type: tok });
    } else if (tok.startsWith('"')) {
      tokens.push({ type: 'string', value: tok.slice(1, -1) });
    } else {
      tokens.push({ type: 'ident', value: tok });
    }
  }

  // Parse: shader_name { ... directives ... }
  let i = 0;
  while (i < tokens.length) {
    const tok = tokens[i];
    if (tok.type === 'ident') {
      const shaderName = tok.value;
      i++;

      // Look for opening brace
      if (i < tokens.length && tokens[i].type === '{') {
        i++;
        const shader = {};
        let foundDiffuse = false;

        // Parse directives until closing brace
        while (i < tokens.length && tokens[i].type !== '}') {
          const directive = tokens[i];
          if (directive.type === 'ident' && directive.value === 'map') {
            i++;
            // Next token should be the map path
            if (i < tokens.length) {
              const mapVal = tokens[i];
              const mapPath = mapVal.type === 'string'
                ? mapVal.value
                : (mapVal.type === 'ident' ? mapVal.value : '');

              // Skip $lightmap, look for actual texture maps
              if (mapPath && !mapPath.startsWith('$')) {
                if (!foundDiffuse) {
                  // First non-lightmap becomes the diffuse
                  shader.diffuseMap = mapPath;
                  foundDiffuse = true;
                }
              }
            }
          }
          i++;
        }

        if (shader.diffuseMap) {
          shaders.set(shaderName, shader);
        }

        // Skip closing brace
        if (i < tokens.length && tokens[i].type === '}') {
          i++;
        }
      }
    } else {
      i++;
    }
  }

  return shaders;
}

/**
 * Load and parse all shader scripts from a collection of assets.
 *
 * @param {Map<string, ArrayBuffer>} assets — map from asset paths to buffers
 * @returns {Map<string, object>} — shader definitions indexed by shader name
 */
export async function loadShadersFromAssets(assets) {
  const allShaders = new Map();

  // Find all .shader files in assets
  for (const [path, buffer] of assets) {
    if (!path.endsWith('.shader')) continue;

    try {
      const text = new TextDecoder('utf-8').decode(buffer);
      const shaders = parseShaderScript(text);
      for (const [name, def] of shaders) {
        allShaders.set(name, def);
      }
    } catch (err) {
      console.warn(`Failed to parse shader ${path}:`, err);
    }
  }

  return allShaders;
}

/**
 * Map a BSP texture name to a diffuse texture path using shader definitions.
 * Returns the path or null if no shader/texture found.
 *
 * Shader name format: "textures/category/name"
 * BSP texture name: "textures/category/name" (usually, but check shader files)
 */
export function getTextureFromShader(bspTextureName, shaderDefs) {
  if (!shaderDefs.has(bspTextureName)) return null;
  const shader = shaderDefs.get(bspTextureName);
  return shader.diffuseMap || null;
}
