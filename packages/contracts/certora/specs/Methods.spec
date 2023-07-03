using AssetMappingsHarness as _AssetMappingsHarness;

////////////////////////////////////// METHODS //////////////////////////////////////

methods {    
    // AssetMappingsHarness 
    function _AssetMappingsHarness.getRevisionHarness() external returns (uint256) envfree;
    function _AssetMappingsHarness.assetMappingsBorrowingEnabled(address) external returns (bool) envfree;
    function _AssetMappingsHarness.assetMappingsBaseLTV(address) external returns (uint64) envfree;

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