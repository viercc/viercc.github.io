'use strict';
document.addEventListener("DOMContentLoaded", function() {
    const mathElements =
        document.createNodeIterator(
            document.body,
            NodeFilter.SHOW_ELEMENT,
            (n) => n.classList.contains("math")
        );
    const mathBlockElements =
        document.createNodeIterator(
            document.body,
            NodeFilter.SHOW_ELEMENT,
            (n) => n.classList.contains("math-block")
        );
    let macros = {};
    let renderElem = (content, targetElem, isDisplay) => {
        katex.render(content, targetElem, {
            "displayMode": isDisplay,
            "macros": macros,
            "throwOnError": false,
            "errorColor": "#DD0000"
        });
    };
    while (1) {
        let elem = mathBlockElements.nextNode();
        if (!elem) break;
        let insertedElem = document.createElement("span");
        elem.parentNode.insertBefore(insertedElem, elem);
        elem.childNodes.forEach((childElem) => {
            if (childElem.nodeType === Node.ELEMENT_NODE && childElem.tagName === "CODE") {
                renderElem(childElem.textContent, insertedElem, true);
            }
        });
    }
    while (1) {
        let elem = mathElements.nextNode();
        if (!elem) break;
        renderElem(elem.textContent, elem, elem.classList.contains("display"));
    }
});
