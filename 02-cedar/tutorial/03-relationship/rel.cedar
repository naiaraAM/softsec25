permit(
  principal, 
  action in [Action::"view", Action::"edit", Action::"delete"], 
  resource 
)
when {
  resource.owner == principal.id || resource.dept == principal.dept
};