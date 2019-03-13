// Parses the development applications at the South Australian District Council of Tumby Bay web
// site and places them in a database.
//
// Michael Bone
// 11th March 2019

"use strict";

import * as fs from "fs";
import * as cheerio from "cheerio";
import * as request from "request-promise-native";
import * as sqlite3 from "sqlite3";
import * as urlparser from "url";
import * as moment from "moment";
import * as pdfjs from "pdfjs-dist";
import didYouMean, * as didyoumean from "didyoumean2";

sqlite3.verbose();

const DevelopmentApplicationsUrl = "https://www.tumbybay.sa.gov.au/page.aspx?u=140";
const CommentUrl = "mailto:dctumby@tumbybay.sa.gov.au";

const Tolerance = 3;

declare const process: any;

// All valid street names, street suffixes, suburb names and hundred names.

let StreetNames = null;
let StreetSuffixes = null;
let SuburbNames = null;
let HundredNames = null;

// Sets up an sqlite database.

async function initializeDatabase() {
    return new Promise((resolve, reject) => {
        let database = new sqlite3.Database("data.sqlite");
        database.serialize(() => {
            database.run("create table if not exists [data] ([council_reference] text primary key, [address] text, [description] text, [info_url] text, [comment_url] text, [date_scraped] text, [date_received] text)");
            resolve(database);
        });
    });
}

// Inserts a row in the database if the row does not already exist.

async function insertRow(database, developmentApplication) {
    return new Promise((resolve, reject) => {
        let sqlStatement = database.prepare("insert or ignore into [data] values (?, ?, ?, ?, ?, ?, ?)");
        sqlStatement.run([
            developmentApplication.applicationNumber,
            developmentApplication.address,
            developmentApplication.description,
            developmentApplication.informationUrl,
            developmentApplication.commentUrl,
            developmentApplication.scrapeDate,
            developmentApplication.receivedDate
        ], function(error, row) {
            if (error) {
                console.error(error);
                reject(error);
            } else {
                if (this.changes > 0)
                    console.log(`    Inserted: application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\" and received date \"${developmentApplication.receivedDate}\" into the database.`);
                else
                    console.log(`    Skipped: application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\" and received date \"${developmentApplication.receivedDate}\" because it was already present in the database.`);
                sqlStatement.finalize();  // releases any locks
                resolve(row);
            }
        });
    });
}

// A bounding rectangle.

interface Rectangle {
    x: number,
    y: number,
    width: number,
    height: number
}

// An element (consisting of text and a bounding rectangle) in a PDF document.

interface Element extends Rectangle {
    text: string
}

// Gets the highest Y co-ordinate of all elements that are considered to be in the same row as
// the specified element.  Take care to avoid extremely tall elements (because these may otherwise
// be considered as part of all rows and effectively force the return value of this function to
// the same value, regardless of the value of startElement).

function getRowTop(elements: Element[], startElement: Element) {
    let top = startElement.y;
    for (let element of elements)
        if (element.y < startElement.y + startElement.height && element.y + element.height > startElement.y)  // check for overlap
            if (getVerticalOverlapPercentage(startElement, element) > 50)  // avoids extremely tall elements
                if (element.y < top)
                    top = element.y;
    return top;
}

// Constructs a rectangle based on the intersection of the two specified rectangles.

function intersect(rectangle1: Rectangle, rectangle2: Rectangle): Rectangle {
    let x1 = Math.max(rectangle1.x, rectangle2.x);
    let y1 = Math.max(rectangle1.y, rectangle2.y);
    let x2 = Math.min(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width);
    let y2 = Math.min(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height);
    if (x2 >= x1 && y2 >= y1)
        return { x: x1, y: y1, width: x2 - x1, height: y2 - y1 };
    else
        return { x: 0, y: 0, width: 0, height: 0 };
}

// Calculates the square of the Euclidean distance between two elements.

function calculateDistance(element1: Element, element2: Element) {
    let point1 = { x: element1.x + element1.width, y: element1.y + element1.height / 2 };
    let point2 = { x: element2.x, y: element2.y + element2.height / 2 };
    if (point2.x < point1.x - element1.width / 5)  // arbitrary overlap factor of 20% (ie. ignore elements that overlap too much in the horizontal direction)
        return Number.MAX_VALUE;
    return (point2.x - point1.x) * (point2.x - point1.x) + (point2.y - point1.y) * (point2.y - point1.y);
}

// Determines whether there is vertical overlap between two elements.

function isVerticalOverlap(element1: Element, element2: Element) {
    return element2.y < element1.y + element1.height && element2.y + element2.height > element1.y;
}

// Gets the percentage of vertical overlap between two elements (0 means no overlap and 100 means
// 100% overlap; and, for example, 20 means that 20% of the second element overlaps somewhere
// with the first element).

function getVerticalOverlapPercentage(element1: Element, element2: Element) {
    let y1 = Math.max(element1.y, element2.y);
    let y2 = Math.min(element1.y + element1.height, element2.y + element2.height);
    return (y2 < y1) ? 0 : (((y2 - y1) * 100) / element2.height);
}

// Gets the element immediately to the right of the specified element (but ignores elements that
// appear after a large horizontal gap).

function getRightElement(elements: Element[], element: Element) {
    let closestElement: Element = { text: undefined, x: Number.MAX_VALUE, y: Number.MAX_VALUE, width: 0, height: 0 };
    for (let rightElement of elements)
        if (isVerticalOverlap(element, rightElement) &&  // ensure that there is at least some vertical overlap
            getVerticalOverlapPercentage(element, rightElement) > 50 &&  // avoid extremely tall elements (ensure at least 50% overlap)
            (rightElement.x + Tolerance > element.x + element.width) &&  // ensure the element actually is to the right (within the specified tolerance)
            (rightElement.x - (element.x + element.width) < 30) &&  // avoid elements that appear after a large gap (arbitrarily ensure less than a 30 pixel gap horizontally)
            calculateDistance(element, rightElement) < calculateDistance(element, closestElement))  // check if closer than any element encountered so far
            closestElement = rightElement;
    return (closestElement.text === undefined) ? undefined : closestElement;
}

// Finds the element that most closely matches the specified text.

function findElement(elements: Element[], text: string, shouldSelectRightmostElement: boolean, shouldSelectLastMatch: boolean) {
    // Examine all the elements on the page that being with the same character as the requested
    // text.
    
    let condensedText = text.replace(/[\s,\-_]/g, "").toLowerCase();
    let firstCharacter = condensedText.charAt(0);

    let matches = [];
    for (let element of elements.filter(element => element.text.trim().toLowerCase().startsWith(firstCharacter))) {
        // Extract up to 5 elements to the right of the element that has text starting with the
        // required character (and so may be the start of the requested text).  Join together the
        // elements to the right in an attempt to find the best match to the text.

        let rightElement = element;
        let rightElements: Element[] = [];

        do {
            rightElements.push(rightElement);

            let currentText = rightElements.map(element => element.text).join("").replace(/[\s,\-_]/g, "").toLowerCase();

            if (currentText.length > condensedText.length + 2)  // stop once the text is too long
                break;
            if (currentText.length >= condensedText.length - 2) {  // ignore until the text is close to long enough
                if (currentText === condensedText)
                    matches.push({ leftElement: rightElements[0], rightElement: rightElement, threshold: 0, text: currentText });
                else if (didYouMean(currentText, [ condensedText ], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true }) !== null)
                    matches.push({ leftElement: rightElements[0], rightElement: rightElement, threshold: 1, text: currentText });
                else if (didYouMean(currentText, [ condensedText ], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 2, trimSpaces: true }) !== null)
                    matches.push({ leftElement: rightElements[0], rightElement: rightElement, threshold: 2, text: currentText });
            }

            rightElement = getRightElement(elements, rightElement);
        } while (rightElement !== undefined && rightElements.length < 5);  // up to 5 elements
    }

    // Chose the best match (if any matches were found).  Note that trimming is performed here so
    // that text such as "  Plan" is matched in preference to text such as "plan)" (when looking
    // for elements that match "Plan").  For an example of this problem see "200/303/07" in
    // "https://www.walkerville.sa.gov.au/webdata/resources/files/DA%20Register%20-%202007.pdf".
    //
    // Note that if the match is made of several elements then sometimes the caller requires the
    // left most element and sometimes the right most element (depending on where further text
    // will be searched for relative to this "found" element).

    if (matches.length > 0) {
        let bestMatch = undefined;

        if (shouldSelectLastMatch)
            bestMatch = matches.reduce((previous, current) =>
                (previous === undefined ||
                current.threshold <= previous.threshold ||
                (current.threshold === previous.threshold && Math.abs(current.text.trim().length - condensedText.length) < Math.abs(previous.text.trim().length - condensedText.length)) ? current : previous), undefined);
        else
            bestMatch = matches.reduce((previous, current) =>
                (previous === undefined ||
                current.threshold < previous.threshold ||
                (current.threshold === previous.threshold && Math.abs(current.text.trim().length - condensedText.length) < Math.abs(previous.text.trim().length - condensedText.length)) ? current : previous), undefined);

        return shouldSelectRightmostElement ? bestMatch.rightElement : bestMatch.leftElement;
    }

    return undefined;
}

// Finds the start element of each development application on the current PDF page (there are
// typically two development applications on a single page and each development application
// typically begins with the text "Building Details").

function findStartElements(elements: Element[]) {
    // Examine all the elements on the page that being with "B" or "b".
    
    let startElements: Element[] = [];
    for (let element of elements.filter(element => element.text.trim().toLowerCase().startsWith("b"))) {
        // Extract up to 4 elements to the right of the element that has text starting with
        // the letter "b" (and so may be the start of the "Building Details" text).  Join
        // together the elements to the right in an attempt to find the best match to the
        // text "Building Details".

        let rightElement = element;
        let rightElements: Element[] = [];
        let matches = [];

        do {
            rightElements.push(rightElement);
        
            let text = rightElements.map(element => element.text).join("").replace(/[\s,\-_]/g, "").toLowerCase();
            if (text.length >= 17)  // stop once the text is too long
                break;
            if (text.length >= 13) {  // ignore until the text is close to long enough
                if (text === "buildingdetails")
                    matches.push({ element: rightElement, threshold: 0, text: text });
                else if (didYouMean(text, [ "BuildingDetails" ], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true }) !== null)
                    matches.push({ element: rightElement, threshold: 1, text: text });
            }

            rightElement = getRightElement(elements, rightElement);
        } while (rightElement !== undefined && rightElements.length < 5);  // up to 5 elements

        // Chose the best match (if any matches were found).

        if (matches.length > 0) {
            let bestMatch = matches.reduce((previous, current) =>
                (previous === undefined ||
                current.threshold < previous.threshold ||
                (current.threshold === previous.threshold && Math.abs(current.text.trim().length - "BuildingDetails".length) < Math.abs(previous.text.trim().length - "BuildingDetails".length)) ? current : previous), undefined);
            startElements.push(bestMatch.element);
        }
    }

    // Ensure the start elements are sorted in the order that they appear on the page.

    let yComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : 0);
    startElements.sort(yComparer);
    return startElements;
}

// Gets the text to the right in a rectangle, where the rectangle is delineated by the positions
// in which the three specified strings of (case sensitive) text are found.

function getRightText(elements: Element[], topLeftText: string, rightText: string, bottomText: string) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.

    let topLeftElement = findElement(elements, topLeftText, true, false);
    let rightElement = (rightText === undefined) ? undefined : findElement(elements, rightText, false, false);
    let bottomElement = (bottomText === undefined) ? undefined : findElement(elements, bottomText, false, false);
    if (topLeftElement === undefined)
        return undefined;

    let x = topLeftElement.x + topLeftElement.width;
    let y = topLeftElement.y;
    let width = (rightElement === undefined) ? Number.MAX_VALUE : (rightElement.x - x);
    let height = (bottomElement === undefined) ? Number.MAX_VALUE : (bottomElement.y - y);

    let bounds: Rectangle = { x: x, y: y, width: width, height: height };

    // Gather together all elements that are at least 50% within the bounding rectangle.

    let intersectingElements: Element[] = []
    for (let element of elements) {
        let intersectingBounds = intersect(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 2 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }
    if (intersectingElements.length === 0)
        return undefined;

    // Sort the elements by Y co-ordinate and then by X co-ordinate.

    let elementComparer = (a: Element, b: Element) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);

    // Join the elements into a single string.

    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}

// Gets the text to the left in a rectangle, where the rectangle is delineated by the positions
// in which the three specified strings of (case sensitive) text are found.

function getLeftText(elements: Element[], topRightText: string, leftText: string, bottomText: string) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.

    let topRightElement = findElement(elements, topRightText, true, false);
    let leftElement = (leftText === undefined) ? undefined : findElement(elements, leftText, false, false);
    let bottomElement = (bottomText === undefined) ? undefined : findElement(elements, bottomText, false, false);
    if (topRightElement === undefined || leftElement === undefined || bottomElement === undefined)
        return undefined;

    let x = leftElement.x + leftElement.width;
    let y = topRightElement.y;
    let width = topRightElement.x - x;
    let height = bottomElement.y - y;

    let bounds: Rectangle = { x: x, y: y, width: width, height: height };

    // Gather together all elements that are at least 50% within the bounding rectangle.

    let intersectingElements: Element[] = []
    for (let element of elements) {
        let intersectingBounds = intersect(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 2 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }
    if (intersectingElements.length === 0)
        return undefined;

    // Sort the elements by Y co-ordinate and then by X co-ordinate.

    let elementComparer = (a: Element, b: Element) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);

    // Join the elements into a single string.

    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}

// Gets the text downwards in a rectangle, where the rectangle is delineated by the positions in
// which the three specified strings of (case sensitive) text are found.

function getDownText(elements: Element[], topText: string, shouldSelectLastMatch: boolean, rightText: string, bottomText: string, optionalBottomText: string) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.

    let topElement = findElement(elements, topText, false, shouldSelectLastMatch);
    let rightElement = (rightText === undefined) ? undefined : findElement(elements, rightText, false, false);
    let bottomElement = (bottomText === undefined) ? undefined : findElement(elements, bottomText, false, false);
    let optionalBottomElement = (optionalBottomText === undefined) ? undefined : findElement(elements, optionalBottomText, false, true);  // select the last match because there may be multiple page breaks containing the text "Page:"
    if (topElement === undefined)
        return undefined;
    
    // The optional bottom element corresponds to a page footer which could appear at any point.
    // If it appears higher then the topText then it should be ignored, otherwise, if it appears
    // lower then the topText then it should be used as the bottommost element (no elements below
    // this element should be extracted).  So it is in this sense that it is "optional".

    if (optionalBottomElement !== undefined) {
        if (optionalBottomElement.y + optionalBottomElement.height < topElement.y)
            optionalBottomElement = undefined;  // ignore the optional bottom text
        else
            bottomElement = optionalBottomElement;
    }

    let x = topElement.x;
    let y = topElement.y + topElement.height;
    let width = (rightElement === undefined) ? Number.MAX_VALUE : (rightElement.x - x);
    let height = (bottomElement === undefined) ? Number.MAX_VALUE : (bottomElement.y - y);

    let bounds: Rectangle = { x: x, y: y, width: width, height: height };

    // Gather together all elements that are at least 25% within the bounding rectangle.  This
    // was changed from 50% to 25% for the District Council of Tumby Bay where elements were
    // joined together with a large number of spaces between.  For example, see the following:
    //
    //     https://www.tumbybay.sa.gov.au/webdata/resources/files/Register%20of%20Development%20Listing%202014.pdf
    //
    // In this PDF the Certifier was joined with the Property Details producing the following:
    //
    //     "District Council of Tumby Bay                Lot 201 Thuruna Road TUMBY BAY"

    let intersectingElements: Element[] = []
    for (let element of elements) {
        let intersectingBounds = intersect(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 4 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }
    if (intersectingElements.length === 0)
        return undefined;

    // Sort the elements by Y co-ordinate and then by X co-ordinate.

    let elementComparer = (a: Element, b: Element) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);

    // Join the elements into a single string.

    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}

// Parses the details from the elements associated with a single development application.

function parseApplicationElements(elements: Element[], startElement: Element, informationUrl: string) {
    // Get the application number.

    let applicationNumber = getDownText(elements, "Document", false, "Applicant Name/", "Wall Type:", undefined);
    if (applicationNumber === undefined || applicationNumber === "") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the application number on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }
    console.log(`    Found \"${applicationNumber}\".`);

    // Get the address.

    let address = getDownText(elements, "Property Details", true, undefined, undefined, "Page:");
    if (address === undefined)
    {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Application number ${applicationNumber} will be ignored because there is no address.  Elements: ${elementSummary}`);
        return undefined;
    }

    // Allow for joined together elements (ie. the Certifier joined with the Property Details).

    address = address.replace(/^District Council of Tumby Bay /gi, "").trim();

    // Allow for the "Page:" text in page footers being joined into the address.

    let pageIndex = address.search(/ p\s*a\s*g\s*e\s*:/i);
    if (pageIndex >= 0)
        address = address.substring(0, pageIndex);

    if (address === "")
    {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Application number ${applicationNumber} will be ignored because the address is blank.  Elements: ${elementSummary}`);
        return undefined;
    }

    // Get the received date.

    let receivedDate: moment.Moment = undefined;
    let receivedDateText = getDownText(elements, "Received", true, "Final", undefined, "Page:");
    receivedDate = (receivedDateText === undefined) ? moment.invalid() : moment(receivedDateText.trim().substring(0, 10), "D/MM/YYYY", true);
    if (!receivedDate.isValid()) {
        receivedDateText = getDownText(elements, "Received", false, "Final", undefined, "Page:");
        receivedDate = (receivedDateText === undefined) ? moment.invalid() : moment(receivedDateText.trim().substring(0, 10), "D/MM/YYYY", true);
    }

    // Get the description.

    let description = getRightText(elements, "Building Type", "Work Type:", "Current Area:");

    // Remove the numeric prefix present in most descriptions.  For example, "60 Shed - Rural".

    if (description !== undefined)
        description = description.replace(/^\d\d /, "");
        
    // Construct the resulting application information.
    
    return {
        applicationNumber: applicationNumber,
        address: address,
        description: ((description !== undefined && description.trim() !== "") ? description : "No Description Provided"),
        informationUrl: informationUrl,
        commentUrl: CommentUrl,
        scrapeDate: moment().format("YYYY-MM-DD"),
        receivedDate: (receivedDate !== undefined && receivedDate.isValid()) ? receivedDate.format("YYYY-MM-DD") : ""
    };
}

// Parses the development applications in the specified date range.

async function parsePdf(url: string) {
    console.log(`Reading development applications from ${url}.`);

    let developmentApplications = [];

    // Read the PDF.

    let buffer = await request({ url: url, encoding: null, rejectUnauthorized: false, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);

    // Parse the PDF.  Each page has the details of multiple applications.  Note that the PDF is
    // re-parsed on each iteration of the loop (ie. once for each page).  This then avoids large
    // memory usage by the PDF (just calling page._destroy() on each iteration of the loop appears
    // not to be enough to release all memory used by the PDF parsing).

    let elements: Element[] = [];
    let pageVerticalOffset = 0;
    for (let pageIndex = 0; pageIndex < 500; pageIndex++) {  // limit to an arbitrarily large number of pages (to avoid any chance of an infinite loop)
        let pdf = await pdfjs.getDocument({ data: buffer, disableFontFace: true, ignoreErrors: true });
        if (pageIndex >= pdf.numPages)
            break;

        console.log(`Reading and parsing applications from page ${pageIndex + 1} of ${pdf.numPages}.`);
        let page = await pdf.getPage(pageIndex + 1);
        let textContent = await page.getTextContent();
        let viewport = await page.getViewport(1.0);
    
        let pageElements: Element[] = textContent.items.map(item => {
            let transform = pdfjs.Util.transform(viewport.transform, item.transform);
    
            // Work around the issue https://github.com/mozilla/pdf.js/issues/8276 (heights are
            // exaggerated).  The problem seems to be that the height value is too large in some
            // PDFs.  Provide an alternative, more accurate height value by using a calculation
            // based on the transform matrix.
    
            let workaroundHeight = Math.sqrt(transform[2] * transform[2] + transform[3] * transform[3]);
            return { text: item.str, x: transform[4], y: transform[5], width: item.width, height: workaroundHeight };
        });

        // Release the memory used by the PDF now that it is no longer required (it will be
        // re-parsed on the next iteration of the loop for the next page).

        await pdf.destroy();
        if (global.gc)
            global.gc();

        // Sort the elements by Y co-ordinate and then by X co-ordinate.

        let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
        pageElements.sort(elementComparer);

        // Ensure that elements on subsequent pages have lower Y co-ordinates than elements on
        // earlier pages.

        let lowestPageElement = pageElements.reduce(((previous, current) => (previous === undefined || current.y + current.height > previous.y + previous.height) ? current : previous), undefined);
        let lowestPageElementY = lowestPageElement.y + lowestPageElement.height;

        for (let pageElement of pageElements)
            pageElement.y += pageVerticalOffset;

        pageVerticalOffset += lowestPageElementY + Tolerance;

        elements = elements.concat(pageElements);
    }

    // Group the elements into sections based on where the "Application No" text starts.

    let applicationElementGroups = [];
    let startElements = findStartElements(elements);
    for (let index = 0; index < startElements.length; index++) {
        // Determine the highest Y co-ordinate of this row and the next row (or the bottom of
        // the current page).  Allow some leeway vertically (add some extra height) because
        // in some cases the lodged date might be higher up than the "Application No" text.
        
        let startElement = startElements[index];
        let raisedStartElement: Element = {
            text: startElement.text,
            x: startElement.x,
            y: startElement.y - startElement.height / 2,  // leeway
            width: startElement.width,
            height: startElement.height };
        let rowTop = getRowTop(elements, raisedStartElement);
        let nextRowTop = (index + 1 < startElements.length) ? getRowTop(elements, startElements[index + 1]) : Number.MAX_VALUE;

        // Extract all elements between the two rows.

        applicationElementGroups.push({ startElement: startElements[index], elements: elements.filter(element => element.y >= rowTop && element.y + element.height < nextRowTop) });
    }

    // Parse the development application from each group of elements (ie. a section of the
    // current page of the PDF document).

    for (let applicationElementGroup of applicationElementGroups) {
        let developmentApplication = parseApplicationElements(applicationElementGroup.elements, applicationElementGroup.startElement, url);
        if (developmentApplication !== undefined)
            if (!developmentApplications.some(otherDevelopmentApplication => otherDevelopmentApplication.applicationNumber === developmentApplication.applicationNumber))  // avoid duplicates
                developmentApplications.push(developmentApplication);
    }

    return developmentApplications;
}

// Gets a random integer in the specified range: [minimum, maximum).

function getRandom(minimum: number, maximum: number) {
    return Math.floor(Math.random() * (Math.floor(maximum) - Math.ceil(minimum))) + Math.ceil(minimum);
}

// Pauses for the specified number of milliseconds.

function sleep(milliseconds: number) {
    return new Promise(resolve => setTimeout(resolve, milliseconds));
}

// Parses the development applications.

async function main() {
    // Ensure that the database exists.

    let database = await initializeDatabase();

    // Read the files containing all possible street names, street suffixes, suburb names and
    // hundred names.

    StreetNames = {};
    for (let line of fs.readFileSync("streetnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetNameTokens = line.toUpperCase().split(",");
        let streetName = streetNameTokens[0].trim();
        let suburbName = streetNameTokens[1].trim();
        (StreetNames[streetName] || (StreetNames[streetName] = [])).push(suburbName);  // several suburbs may exist for the same street name
    }

    StreetSuffixes = {};
    for (let line of fs.readFileSync("streetsuffixes.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetSuffixTokens = line.toUpperCase().split(",");
        StreetSuffixes[streetSuffixTokens[0].trim()] = streetSuffixTokens[1].trim();
    }

    SuburbNames = {};
    for (let line of fs.readFileSync("suburbnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let suburbTokens = line.toUpperCase().split(",");
        SuburbNames[suburbTokens[0].trim()] = suburbTokens[1].trim();
    }

    HundredNames = [];
    for (let line of fs.readFileSync("hundrednames.txt").toString().replace(/\r/g, "").trim().split("\n"))
        HundredNames.push(line.trim().toUpperCase());

    // Read the main page of development applications.

    console.log(`Retrieving page: ${DevelopmentApplicationsUrl}`);

    let body = await request({ url: DevelopmentApplicationsUrl, rejectUnauthorized: false, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    let $ = cheerio.load(body);

    let pdfUrls: string[] = [];
    for (let element of $("div.unityHtmlArticle p a").get()) {
        let pdfUrl = new urlparser.URL(element.attribs.href, DevelopmentApplicationsUrl).href
        if (pdfUrl.toLowerCase().includes("register") && pdfUrl.toLowerCase().includes(".pdf"))
            if (!pdfUrls.some(url => url === pdfUrl))
                pdfUrls.push(pdfUrl);
    }

    // Always parse the most recent PDF file and randomly select one other PDF file to parse.

    if (pdfUrls.length === 0) {
        console.log("No PDF files were found on the page.");
        return;
    }

    console.log(`Found ${pdfUrls.length} PDF file(s).  Selecting two to parse.`);

    // Select the most recent PDF.  And randomly select one other PDF (avoid processing all PDFs
    // at once because this may use too much memory, resulting in morph.io terminating the current
    // process).

    // let selectedPdfUrls: string[] = [];
    // selectedPdfUrls.push(pdfUrls.shift());
    // if (pdfUrls.length > 0)
    //     selectedPdfUrls.push(pdfUrls[getRandom(0, pdfUrls.length)]);
    // if (getRandom(0, 2) === 0)
    //     selectedPdfUrls.reverse();

    // for (let pdfUrl of ["https://www.tumbybay.sa.gov.au/webdata/resources/files/2016%20Website%20Register%20of%20Development%20Application%20Listing-5.pdf"]) {
    for (let pdfUrl of pdfUrls) {
        console.log(`Parsing document: ${pdfUrl}`);
        let developmentApplications = await parsePdf(pdfUrl);
        console.log(`Parsed ${developmentApplications.length} development application(s) from document: ${pdfUrl}`);

        // Attempt to avoid reaching 512 MB memory usage (this will otherwise result in the
        // current process being terminated by morph.io).

        if (global.gc)
            global.gc();

        console.log(`Inserting development applications into the database.`);
        for (let developmentApplication of developmentApplications)
            await insertRow(database, developmentApplication);
    }
}

main().then(() => console.log("Complete.")).catch(error => console.error(error));
