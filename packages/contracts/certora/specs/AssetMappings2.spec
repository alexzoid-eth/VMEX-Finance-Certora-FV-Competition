import "./methods/erc20Methods.spec";
import "./Methods.spec";

////////////////////////////////////// DEFINITIONS //////////////////////////////////////

// `PercentageMath.PERCENTAGE_FACTOR`
definition PERCENTAGE_FACTOR() returns uint64 = 10^18;

// `PercentageMath.HALF_PERCENT`
definition HALF_PERCENT() returns uint64 = require_uint64(PERCENTAGE_FACTOR() / 2);

// `PercentageMath.convertToPercent()`
definition CONVERTED_TO_PERCENT_MIN_VALUE() returns uint64 = 10^14;

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

/**
* @notice Trying to hook the whole structure in one hook generates this error
* Encountered an unexpected error in Prover, please report in certora.com. Error code 3213395558. Error message: Rule oneAssetRecordCouldBeModified timed-out
* https://prover.certora.com/output/50375/22b99fc2619b4f009f63c212fea7c4aa/?anonymousKey=15d7a7f83916c365f9e92b13eebe9a654cf80bf0
**/
/*
hook Sstore assetMappings[KEY address asset].(offset 0) AssetMappings.AssetData val STORAGE { }
*/

/**
* @notice Using a lot of hooks caused to timeouts, trying to hook slots writing
* TODO: cannot force to work it well, moved to separate hooks instead
*/

/*
struct AssetData {

    // 0-32 bytes
    uint128 supplyCap;
    uint128 borrowCap;

    // 32-64 bytes
    uint64 baseLTV;
    uint64 liquidationThreshold; 
    uint64 liquidationBonus; 
    uint64 borrowFactor; 

    // 64-96 bytes
    bool borrowingEnabled;
    bool isAllowed;
    bool exists;
    uint8 assetType;
    uint64 VMEXReserveFactor; 
    address nextApprovedAsset;
}
*/
/*
hook Sstore assetMappings[KEY address asset].(offset 32) uint256 val STORAGE {
        
    // AssetData.baseLTV
    assetBaseLTV[asset] = require_uint64(val & 0xFFFFFFFFFFFFFFFF);  

    // AssetData.liquidationThreshold
    assetLiquidationThreshold[asset] = require_uint64((val >> 64) & 0xFFFFFFFFFFFFFFFF);  

    // AssetData.liquidationBonus
    assetLiquidationBonus[asset] = require_uint64((val >> 128) & 0xFFFFFFFFFFFFFFFF);  

    // AssetData.borrowFactor
    assetBorrowFactor[asset] = require_uint64(val >> 192) & 0xFFFFFFFFFFFFFFFF; 
}

hook Sstore assetMappings[KEY address asset].(offset 64) uint256 val STORAGE {

    // AssetData.borrowingEnabled
    assetBorrowingEnabled[asset] = (val & 0xFF) != 0; 

    // AssetData.isAllowed
    assetAllowed[asset] = ((val >> 8) & 0xFF) != 0; 

    // AssetData.exists
    assetExists[asset] = ((val >> 16) & 0xFF) != 0; 

    // AssetData.assetType
    assetType[asset] = require_uint8((val >> 24) & 0xFF);

    // AssetData.VMEXReserveFactor
    assetVMEXReserveFactor[asset] = require_uint64((val >> 32) & 0xFFFFFFFFFFFFFFFF);  

    // AssetData.nextApprovedAsset
    // TODO: `require_address()` not supported yet
}
*/

hook Sstore assetMappings[KEY address asset].baseLTV uint64 val STORAGE {
    assetBaseLTV[asset] = val;
}

hook Sstore assetMappings[KEY address asset].liquidationThreshold uint64 val STORAGE {
    assetLiquidationThreshold[asset] = val;
}

hook Sstore assetMappings[KEY address asset].liquidationBonus uint64 val STORAGE {
    assetLiquidationBonus[asset] = val;
}

////////////////////////////////////// PROPERTIES //////////////////////////////////////

/**
* @notice  
* Valid state: assset `baseLTV`
**/

invariant reasonableBaseLTV(address asset) 
    (assetLiquidationThreshold[asset] != 0 && assetBaseLTV[asset] != 0) => (
        // `uint256(inputAsset.baseLTV).convertToPercent().toUint64();`
        (assetBaseLTV[asset] >= CONVERTED_TO_PERCENT_MIN_VALUE())
            // `baseLTV <= liquidationThreshold`
            && (assetBaseLTV[asset] <= assetLiquidationThreshold[asset])
    )
    // `configureAssetMapping()` missed important checks which exist in `addAssetMapping()`
    filtered { f -> !VIEW_FUNCTIONS(f) && !CONFIGURE_ASSET_MAPPING_FUNCTION(f) }

/**
* @notice 
* Valid state: assset `liquidationThreshold`
**/

invariant reasonableLiquidationThreshold(address asset) 
    (assetLiquidationThreshold[asset] != 0) => (
        // `uint256(inputAsset.liquidationThreshold).convertToPercent().toUint64();`
        (assetLiquidationThreshold[asset] >= CONVERTED_TO_PERCENT_MIN_VALUE()
            // `uint256(liquidationThreshold).percentMul(uint256(liquidationBonus)) <= PercentageMath.PERCENTAGE_FACTOR`
            && (assetLiquidationBonus[asset] != 0)
            && (assetLiquidationThreshold[asset] <= require_uint64(((max_uint256) - HALF_PERCENT()) / assetLiquidationBonus[asset]))
            && (require_uint64((assetLiquidationThreshold[asset] * assetLiquidationBonus[asset] + HALF_PERCENT()) / PERCENTAGE_FACTOR()) <= PERCENTAGE_FACTOR()))
    )
    filtered { f -> !VIEW_FUNCTIONS(f) && !CONFIGURE_ASSET_MAPPING_FUNCTION(f) }

/**
* @notice 
* Valid state: asset `liquidationBonus`
**/

invariant reasonableLiquidationBonus(address asset) (assetLiquidationBonus[asset] != 0) => (
        (assetLiquidationThreshold[asset] != 0)
            // `uint256(liquidationBonus) > PercentageMath.PERCENTAGE_FACTOR`
            ? (assetLiquidationBonus[asset] > PERCENTAGE_FACTOR())
            // `uint256(inputAsset.liquidationThreshold).convertToPercent().toUint64();`
            : (assetLiquidationBonus[asset] >= CONVERTED_TO_PERCENT_MIN_VALUE())
    )
    filtered { f -> !VIEW_FUNCTIONS(f) && !CONFIGURE_ASSET_MAPPING_FUNCTION(f) }


