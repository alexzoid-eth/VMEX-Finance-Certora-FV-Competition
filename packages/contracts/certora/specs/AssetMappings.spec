import "./methods/erc20Methods.spec";

/////////////////// METHODS ////////////////////////

methods {
    // getters
    function assetMappings(address) internal;

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
/*
ghost mapping (address => uint64) assetLiqBonus {
    init_state axiom forall address asset. assetLiqBonus[asset] == 0;
}

hook Sload uint64 val assetMappings[KEY address asset].liquidationBonus STORAGE {
    require assetLiqBonus[asset] == val;
}
*/
ghost mapping (address => bool) assetExists {
    init_state axiom forall address asset. assetExists[asset] == false;
}

/*
hook Sload bool val assetMappings[KEY address asset].(offset 66) STORAGE {
    require assetExists[asset] == val;
}
*/

hook Sstore assetMappings[KEY address asset].(offset 66) bool val (bool _old) STORAGE {
    require assetExists[asset] == val;
}

///////////////// PROPERTIES ///////////////////////

/**
* @notice Prove bug1.patch
* Hight level: only global admin could add new asset
**/
rule onlyGlobalAdminCanAddAsset(method f, env e, calldataarg args, address asset) 
    filtered { f -> !f.isView }
{
    bool existsBefore = assetExists[asset];

    f(e, args);

    bool existsAfter = assetExists[asset];

    assert existsAfter != existsBefore;
        //=> e.msg.sender == 331; // 333 set as owner in methods block summary for getGlobalAdmin
}

/*
invariant reasonableLiquidationBonus(address asset) 
    assetExists[asset] => assetLiqBonus[asset] > 10^18;
*/
