import "./methods/erc20Methods.spec";

/////////////////// METHODS ////////////////////////

methods {
    // getters
    function assetMappings(address) internal;
    function approvedAssetsHead() internal;
    function approvedAssetsTail() internal;

    // addressesProvider functions
    function _.getGlobalAdmin() external => ALWAYS(333);
    function _.getLendingPoolConfigurator() external => CONSTANT; 
    function _.getLendingPool() external => CONSTANT;

    // ILendingPoolConfigurator functions
    function _.totalTranches() external => NONDET;

    // Lending Pool functions
    function _.getReserveData(address,uint64) external => DISPATCHER(true);
}

///////////////// DEFINITIONS //////////////////////

////////////////// FUNCTIONS //////////////////////

/**
* @notice Call this in each rule
**/

function setup(env e) {
    require (approvedAssetsHead(e) == 0);
    require (approvedAssetsTail(e) == 0);
}

/**
* @notice Getter for assetMappings[asset].exists
**/

ghost mapping (address => bool) assetExists {
    init_state axiom forall address asset. assetExists[asset] == false;
}

hook Sload bool val assetMappings[KEY address asset].(offset 66) STORAGE {
    require assetExists[asset] == val;
}

hook Sstore assetMappings[KEY address asset].(offset 66) bool val (bool _old) STORAGE {
    assetExists[asset] = val;
}

/**
* @notice Getter for assetMappings[asset].liquidationBonus
**/

ghost mapping (address => uint64) assetLiqBonus {
    init_state axiom forall address asset. assetLiqBonus[asset] == 0;
}

hook Sload uint64 val assetMappings[KEY address asset].liquidationBonus STORAGE {
    require assetLiqBonus[asset] == val;
}

hook Sstore assetMappings[KEY address asset].liquidationBonus uint64 val (uint64 _old) STORAGE {
    assetLiqBonus[asset] = val;
}

///////////////// PROPERTIES ///////////////////////

/**
* @notice Prove bug1.patch
* Hight level: only global admin could add a new asset
**/

rule onlyGlobalAdminCanAddAsset(method f, env e, calldataarg args, address asset) 
{
    setup(e);

    bool before = assetExists[asset];

    f(e, args);

    bool after = assetExists[asset];

    assert before != after
        => e.msg.sender == 333; // 333 set as owner in methods block summary for getGlobalAdmin;
}

/**
* @notice Prove bug2.patch
* Valid state: `liquidationBonus` > 10^18
**/

invariant reasonableLiquidationBonus(address asset) 
    assetExists[asset] => assetLiqBonus[asset] > 10^18;
