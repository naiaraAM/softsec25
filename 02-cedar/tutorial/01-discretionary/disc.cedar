permit(
  principal == User::"alice", 
  action in [Action::"view", Action::"update", Action::"delete"], 
  resource  == Photo::"VacationPhoto94.jpg"
);

permit (
  principal == User::"bob",
  action == Action::"view",
  resource == Photo::"Portrait.jpg"
);

// Do not add any permissions on Bob side for "VacationPhoto94.jpg"