import "./methods/erc20Methods.spec";
import "./Methods.spec";

////////////////////////////////////// DEFINITIONS //////////////////////////////////////

// `view` functions
definition VIEW_FUNCTIONS(method f) returns bool = f.isView || f.isPure;

// `initialize()` function
definition INITIALIZE_FUNCTION(method f) returns bool 
    = f.selector == sig:initialize(address).selector;

// `addAssetMapping()` function
definition ADD_ASSET_MAPPING_FUNCTION(method f) returns bool 
    = f.selector == sig:addAssetMapping(AssetMappings.AddAssetMappingInput[]).selector;

definition CONFIGURE_ASSET_MAPPING_FUNCTION(method f) returns bool 
    = f.selector == sig:configureAssetMapping(address, uint64, uint64, uint64, uint128, uint128, uint64).selector;

////////////////////////////////////// FUNCTIONS //////////////////////////////////////

/**
* @notice `approvedAssetsHead` and `approvedAssetsTail` hooks
**/

ghost address assetsHeadOld {
    init_state axiom assetsHeadOld == 0;
}

ghost address assetsTailOld {
    init_state axiom assetsTailOld == 0;
}

hook Sstore approvedAssetsHead address val (address val_old) STORAGE {
    havoc assetsHeadOld assuming assetsHeadOld@old == 0 && val == 0
        ? assetsHeadOld@old == assetsHeadOld@new : assetsHeadOld@new == val_old;
}

hook Sstore approvedAssetsTail address val (address val_old) STORAGE {
    havoc assetsTailOld assuming assetsTailOld@old == 0 && val == 0
        ? assetsTailOld@old == assetsTailOld@new : assetsTailOld@new == val_old;
}

/**
* @notice assetMappings[asset].AssetData hooks
**/

ghost mapping (address => bool) assetAllowed {
    init_state axiom forall address asset. assetAllowed[asset] == true;
}

ghost mapping (address => bool) assetExists {
    init_state axiom forall address asset. assetExists[asset] == false;
}

ghost address assetOneAddress {
    init_state axiom assetOneAddress == 0;
}

ghost address assetTwoAddress {
    init_state axiom assetTwoAddress == 0;
}

hook Sstore assetMappings[KEY address asset].(offset 32) uint256 val STORAGE {

    // Assuming `asset` is not zero because of `Address.isContract(currentAssetAddress)` check
    require asset != 0;

    // Save first address
    havoc assetOneAddress assuming assetOneAddress@old != 0
        ? assetOneAddress@new == assetOneAddress@old
        : assetOneAddress@new == asset;

    // Save second if it different from the first
    havoc assetTwoAddress assuming asset == assetOneAddress
        ? assetTwoAddress@new == assetTwoAddress@old
        : assetTwoAddress@new == asset;
}

hook Sstore assetMappings[KEY address asset].(offset 64) uint256 val STORAGE {

    // Assuming `asset` is not zero because of `Address.isContract(currentAssetAddress)` check
    require asset != 0;

    // Save first address
    havoc assetOneAddress assuming assetOneAddress@old != 0
        ? assetOneAddress@new == assetOneAddress@old
        : assetOneAddress@new == asset;

    // Save second if it different from the first
    havoc assetTwoAddress assuming asset == assetOneAddress
        ? assetTwoAddress@new == assetTwoAddress@old
        : assetTwoAddress@new == asset;
}

hook Sstore assetMappings[KEY address asset].(offset 65) bool val STORAGE {
    assetAllowed[asset] = val;    
}

hook Sstore assetMappings[KEY address asset].(offset 66) bool val STORAGE {
    assetExists[asset] = val;
}

/**
* @notice VersionedInitializable.* hooks
**/

ghost uint256 lastRevision {
    init_state axiom lastRevision == 0;
}

hook Sstore lastInitializedRevision uint256 val STORAGE {
    havoc lastRevision assuming lastRevision@new == val;
}

hook Sload bool val initializing STORAGE {
    // `initializing` is changed only inside `initialize()` function
    require val == false;
}

////////////////////////////////////// PROPERTIES //////////////////////////////////////

/**
* @notice No patch implemented
* Valid state: revision version is stored in `lastInitializedRevision` as soon as contract 
* is initialized
**/

invariant lastRevisionSolvency() _AssetMappingsHarness.getRevisionHarness() >= lastRevision
    filtered { f -> !VIEW_FUNCTIONS(f) }

/**
* @notice Prove bug1.patch
* Hight level: only global admin can add a new asset
**/

rule onlyGlobalAdminCanAddAsset(method f, env e, calldataarg args, address asset) 
    filtered { f -> !VIEW_FUNCTIONS(f) }
{
    bool before = assetExists[asset];

    f(e, args);

    bool after = assetExists[asset];

    // `333` set as owner in methods block summary for `getGlobalAdmin()`
    assert before != after => e.msg.sender == 333; 
}

/**
* @notice Prove bug2.patch
* High level: only existing record could be modified (don't mean adding new) 
**/

rule existingAssetRecordCouldBeModified(method f, env e, calldataarg args) 
    filtered { f-> !VIEW_FUNCTIONS(f) } {

    require assetOneAddress == 0;

    f(e, args);

    assert assetOneAddress != 0 => isAssetInMappings(e, assetOneAddress); 
}

/**
* @notice Prove bug3.patch
* Unit test: initialization could not not be called twice
**/

rule initializeCalledOnce() {

    env e1;
    address provider1;
    initialize(e1, provider1);

    env e2;
    address provider2;
    initialize@withrevert(e2, provider2);

    // Second call of `initialize()` always reverts
    assert lastReverted;
}

/**
* @notice Prove bug4.patch
* Variable transition: list's head could be changed only once
**/

invariant listSetHeadOnlyOnce() assetsHeadOld == 0
    filtered { f -> !VIEW_FUNCTIONS(f) && !INITIALIZE_FUNCTION(f) } 

/**
* @notice Prove bug5.patch
* Valid state: list's head or tail could not be uninitialized 
**/

invariant listUninitializable(env e) approvedAssetsHead(e) == 0 || approvedAssetsTail(e) == 0 
    => approvedAssetsHead(e) == 0 && approvedAssetsTail(e) == 0 && assetsTailOld == 0
    filtered { f -> !VIEW_FUNCTIONS(f) && !INITIALIZE_FUNCTION(f) } 

/**
* @notice Prove bug6.patch
* High level: only global admin can execute non-view fucntions (`initialize()` is an exception)
**/

rule onlyGlobalAdminCanExecuteNonViewFunctions(method f, env e, calldataarg args) 
    filtered { f -> !VIEW_FUNCTIONS(f) && !INITIALIZE_FUNCTION(f) } {
    
    f@withrevert(e, args);

    // `333` set as owner in methods block summary for `getGlobalAdmin()`
    assert !lastReverted => e.msg.sender == 333;
}

/**
* @notice Prove bug6.patch
* High level: only global admin can modify state (`initialize()` is an exception)
**/

rule onlyGlobalAdminCanModifyState(method f, env e, calldataarg args) 
    filtered { f -> !VIEW_FUNCTIONS(f) && !INITIALIZE_FUNCTION(f) } {
    
    storage before = lastStorage;

    f@withrevert(e, args);

    storage after = lastStorage;

    // `333` set as owner in methods block summary for `getGlobalAdmin()`
    assert !lastReverted && before[currentContract] == after[currentContract]
        => e.msg.sender == 333;
}

/**
* @notice Prove bug7.patch
* High level: only one asset record could be modified (don't mean adding new) at a time
**/

rule oneAssetRecordCouldBeModified(method f, env e, calldataarg args) 
    filtered { f -> !VIEW_FUNCTIONS(f) && !ADD_ASSET_MAPPING_FUNCTION(f) } {

    require assetOneAddress == 0;
    require assetTwoAddress == 0;

    f(e, args);

    assert assetTwoAddress == 0;
}

/**
* @notice 
* Valid state: disallowed assets should meet several criteria in `validateAssetAllowed()`
**/

invariant disallowedAssetsSolvency(env e, address asset) !assetAllowed[asset] => 
        // require(!assetMappings[asset].borrowingEnabled, Errors.AM_UNABLE_TO_DISALLOW_ASSET);
        !_AssetMappingsHarness.assetMappingsBorrowingEnabled(asset) 
        // require(assetMappings[asset].baseLTV == 0, Errors.AM_UNABLE_TO_DISALLOW_ASSET);
        && _AssetMappingsHarness.assetMappingsBaseLTV(asset) == 0
        // TODO: tranches totalSupply() == 0
    filtered { f -> !VIEW_FUNCTIONS(f) }
