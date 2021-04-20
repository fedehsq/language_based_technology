// Task: Copy the contents of boolean variables h1, h2, h3, h4, h5, h6 to l1, l2, l3, l4, l5, l6, respectively.
// A variable is high if its name starts with the letter "h", otherwise it is low.

// 2: Note: Everything is accepted except a direct assignment involving a high variable to a low one.
if (h1) {
    l1 = true;
  } else {
    l1 = false;
  }
  if (h2) {
    l2 = true;
  } else {
    l2 = false;
  }
  if (h3) {
    l3 = true;
  } else {
    l3 = false;
  }
  if (h4) {
    l4 = true;
  } else {
    l4 = false;
  }
  if (h5) {
    l5 = true;
  } else {
    l5 = false;
  }
  if (h6) {
    l6 = true;
  } else {
    l6 = false;
  }


// 3 Note: (i) The value of h1 can be extracted by wrapping it in declassify. (ii) Assigning a declassified value is not allowed in ifs/loops with high guards. (iii) Both branches of an if must have same number of steps. Skip and assignments count as one step each.
l1 = declassify(h1);

h1 = h2;
l2 = declassify(h1);

h1 = h3;
l3 = declassify(h1);

h1 = h4;
l4 = declassify(h1);
  
h1 = h5;
l5 = declassify(h1);
  
h1 = h6;
l6 = declassify(h1);



try {
    l1 = false;
    if (h1) {
      skip;
    } else {
      throw; 
    }
    l1 = true;
  } catch {
    skip;
  }
    try {
    l2 = false;
    if (h2) {
      skip;
    } else {
      throw; 
    }
    l2 = true;
  } catch {
    skip;
  }try {
    l3 = false;
    if (h3) {
      skip;
    } else {
      throw; 
    }
    l3 = true;
  } catch {
    skip;
  }try {
    l4 = false;
    if (h4) {
      skip;
    } else {
      throw; 
    }
    l4 = true;
  } catch {
    skip;
  }try {
    l5 = false;
    if (h5) {
      skip;
    } else {
      throw; 
    }
    l5 = true;
  } catch {
    skip;
  }try {
    l6 = false;
    if (h6) {
      skip;
    } else {
      throw; 
    }
    l6 = true;
  } catch {
    skip;
  }


  let (x = h1) in l1 = x;
let (x = h2) in l2 = x;
let (x = h3) in l3 = x;
let (x = h4) in l4 = x;
let (x = h5) in l5 = x;
let (x = h6) in l6 = x;


declare proc p(in x : low, out y : low) { y = x; }
if (h1) p(true, l1); else p(false, l1);
if (h2) p(true, l2); else p(false, l2);
if (h3) p(true, l3); else p(false, l3);
if (h4) p(true, l4); else p(false, l4);
if (h5) p(true, l5); else p(false, l5);
if (h6) p(true, l6); else p(false, l6);
  
      