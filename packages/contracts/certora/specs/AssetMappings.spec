import "./methods/erc20Methods.spec";

using AssetMappingsHarness as _AssetMappingsHarness;

////////////////////////////////////// METHODS //////////////////////////////////////

methods {    
    // AssetMappingsHarness 
    function _AssetMappingsHarness.getRevisionHarness() external returns (uint256) envfree;
    function _AssetMappingsHarness.assetMappingsBorrowingEnabled(address) external returns (bool) envfree;

    // AssetMappings
    function approvedAssetsHead() internal returns (address);
    function approvedAssetsTail() internal returns (address);
    function getNumApprovedTokens() internal returns (uint256);
    function isAssetInMappings(address) internal returns (bool);

    // VersionedInitializable
    function _VersionedInitializable.lastInitializedRevision() internal;
    function _VersionedInitializable.initializing() internal;

    // addressesProvider functions
    function _.getGlobalAdmin() external => ALWAYS(333);
    function _.getLendingPoolConfigurator() external => CONSTANT; 
    function _.getLendingPool() external => CONSTANT;

    // ILendingPoolConfigurator functions
    function _.totalTranches() external => NONDET;

    // Lending Pool functions
    function _.getReserveData(address,uint64) external => DISPATCHER(true);
}

////////////////////////////////////// DEFINITIONS //////////////////////////////////////

// `PercentageMath.PERCENTAGE_FACTOR`
definition PERCENTAGE_FACTOR() returns mathint = 10^18;

// `PercentageMath.HALF_PERCENT`
definition HALF_PERCENT() returns mathint = PERCENTAGE_FACTOR() / 2;

// `PercentageMath.convertToPercent()`
definition CONVERT_TO_PERCENT_MIN_VALUE() returns uint64 = 10^14;

// `view` functions
definition VIEW_FUNCTIONS(method f) returns bool = f.isView || f.isPure;

// `initialize()` function
definition INITIALIZE_FUNCTION(method f) returns bool 
    = f.selector == sig:initialize(address).selector;

// `addAssetMapping()` function
definition ADD_ASSET_MAPPING_FUNCTION(method f) returns bool 
    = f.selector == sig:addAssetMapping(AssetMappings.AddAssetMappingInput[]).selector;

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

ghost mapping (address => uint64) assetBaseLTV {
    init_state axiom forall address asset. assetBaseLTV[asset] == 0;
}

ghost mapping (address => uint64) assetLiquidationThreshold {
    init_state axiom forall address asset. assetLiquidationThreshold[asset] == 0;
}

ghost mapping (address => uint64) assetLiquidationBonus {
    init_state axiom forall address asset. assetLiquidationBonus[asset] == 0;
}

ghost mapping (address => uint64) assetBorrowFactor {
    init_state axiom forall address asset. assetBorrowFactor[asset] == 0;
}

ghost mapping (address => bool) assetBorrowingEnabled {
    init_state axiom forall address asset. assetBorrowingEnabled[asset] == false;
}

ghost mapping (address => bool) assetAllowed {
    init_state axiom forall address asset. assetAllowed[asset] == true;
}

ghost mapping (address => bool) assetExists {
    init_state axiom forall address asset. assetExists[asset] == false;
}

ghost mapping (address => uint8) assetType {
    init_state axiom forall address asset. assetType[asset] == 0;
}

ghost mapping (address => uint64) assetVMEXReserveFactor {
    init_state axiom forall address asset. assetVMEXReserveFactor[asset] == 0;
}

ghost mapping (address => address) assetNextApprovedAsset {
    init_state axiom forall address asset. assetNextApprovedAsset[asset] == 0;
}

ghost address assetOneAddress {
    init_state axiom assetOneAddress == 0;
}

ghost address assetTwoAddress {
    init_state axiom assetTwoAddress == 0;
}

ghost uint256 approvedTokensNumber {
    init_state axiom approvedTokensNumber == 0;
}

/**
* @notice Trying to hook the whole structure in one hook generates this error
* Encountered an unexpected error in Prover, please report in certora.com. Error code 3213395558. Error message: Rule oneAssetRecordCouldBeModified timed-out
* https://prover.certora.com/output/50375/22b99fc2619b4f009f63c212fea7c4aa/?anonymousKey=15d7a7f83916c365f9e92b13eebe9a654cf80bf0
**/
/*
hook Sstore assetMappings[KEY address asset].(offset 0) AssetMappings.AssetData val STORAGE {
    // Save first address
    havoc assetOneAddress assuming assetOneAddress@old != 0
        ? assetOneAddress@new == assetOneAddress@old
        : assetOneAddress@new == asset;
    // Save second if it different from the first
    havoc assetTwoAddress assuming asset == assetOneAddress
        ? assetTwoAddress@new == assetTwoAddress@old
        : assetTwoAddress@new == asset;
}
*/

/*
struct AssetData {
    uint128 supplyCap;
    uint128 borrowCap;
    ...
}
*/
hook Sstore assetMappings[KEY address asset].(offset 0) uint256 val STORAGE {

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

/*
struct AssetData {
    ...
    uint64 baseLTV;
    uint64 liquidationThreshold; 
    uint64 liquidationBonus; 
    uint64 borrowFactor; 
    ...
}
*/
hook Sstore assetMappings[KEY address asset].(offset 32) uint256 val STORAGE {

    // Assuming `asset` is not zero because of `Address.isContract(currentAssetAddress)` check
    require asset != 0;

    // AssetData.baseLTV
    assetBaseLTV[asset] = require_uint64(val & 0xFFFFFFFFFFFFFFFF);  

    // AssetData.liquidationThreshold
    assetLiquidationThreshold[asset] = require_uint64((val >> 64) & 0xFFFFFFFFFFFFFFFF);  

    // AssetData.liquidationBonus
    assetLiquidationBonus[asset] = require_uint64((val >> 128) & 0xFFFFFFFFFFFFFFFF);  

    // AssetData.borrowFactor
    assetBorrowFactor[asset] = require_uint64(val >> 192); 

    // Save first address
    havoc assetOneAddress assuming assetOneAddress@old != 0
        ? assetOneAddress@new == assetOneAddress@old
        : assetOneAddress@new == asset;

    // Save second if it different from the first
    havoc assetTwoAddress assuming asset == assetOneAddress
        ? assetTwoAddress@new == assetTwoAddress@old
        : assetTwoAddress@new == asset;
}

/*
struct AssetData {
    ...
    bool borrowingEnabled;
    bool isAllowed;
    bool exists;
    uint8 assetType;
    uint64 VMEXReserveFactor; 
    address nextApprovedAsset;
}
*/
hook Sstore assetMappings[KEY address asset].(offset 64) uint256 val STORAGE {

    // Assuming `asset` is not zero because of `Address.isContract(currentAssetAddress)` check
    require asset != 0;

    // AssetData.borrowingEnabled
    assetBorrowingEnabled[asset] = (val & 0x200000) != 0; 

    // AssetData.isAllowed
    assetAllowed[asset] = (val & 0x400000) != 0; 

    // AssetData.exists
    assetExists[asset] = (val & 0x800000) != 0; 

    // AssetData.assetType
    assetType[asset] = require_uint8((val >> 24) & 0xFF);

    // AssetData.VMEXReserveFactor
    assetVMEXReserveFactor[asset] = require_uint64((val >> 32) & 0xFFFFFFFF);  

    // AssetData.nextApprovedAsset
    // TODO: `require_address()` not supported yet
    // assetNextApprovedAsset[asset] = require_address(uint160(val >> 96)); 

    // Save first address
    havoc assetOneAddress assuming assetOneAddress@old != 0
        ? assetOneAddress@new == assetOneAddress@old
        : assetOneAddress@new == asset;

    // Save second if it different from the first
    havoc assetTwoAddress assuming asset == assetOneAddress
        ? assetTwoAddress@new == assetTwoAddress@old
        : assetTwoAddress@new == asset;
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
    // initializing` is changed only inside an `initialize()` function
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

    f@withrevert(e, args);

    assert !lastReverted && assetOneAddress != 0 => isAssetInMappings(e, assetOneAddress); 
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

