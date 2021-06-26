'use strict';
document.addEventListener("DOMContentLoaded", function() {
    const mathElements =
        document.createNodeIterator(
            document.body,
            NodeFilter.SHOW_ELEMENT,
            (n) => n.classList.contains("math")
        );
    let macros = {};
    while (1) {
        let elem = mathElements.nextNode();
        if (!elem) break;
        
        const isDisplay = elem.classList.contains("display");
        katex.render(elem.firstChild.data, elem, {
            "displayMode": isDisplay,
            "macros": macros,
            "throwOnError": false,
            "errorColor": "#DD0000"
        });
    }
});
