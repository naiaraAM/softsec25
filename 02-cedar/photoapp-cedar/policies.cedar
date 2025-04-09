// 1. Any user can see public images.
permit (
    principal,
    action == Action::"view",
    resource
) when {
    resource.isPublic
};

// 2. Any user can view and delete their own images
permit (
    principal, 
    action in [Action::"view", Action::"delete"], 
    resource)
when { resource.owner == principal };

// 3. Admins can delete public images of any user
permit (
    principal,
    action == Action::"delete",
    resource)
when { resource.isPublic && principal in Group::"Admin"};

// 4. Users under the age of 18 (or guests) should not see images marked explicit
forbid (
    principal,
    action == Action::"view",
    resource
) when {
    resource.isExplicit && principal.isMinor
};