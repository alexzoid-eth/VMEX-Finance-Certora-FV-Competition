// SPDX-License-Identifier: agpl-3.0
pragma solidity 0.8.19;

import {AssetMappings} from "../../contracts/protocol/lendingpool/AssetMappings.sol";

/**
 * @title AssetMappings harness contract
 **/
contract AssetMappingsHarness is AssetMappings {

    function getRevisionHarness() external pure returns (uint256) {
        return getRevision();
    }

    function validateAssetAllowedHarness(address asset) view external returns(bool) {
        validateAssetAllowed(asset);
        return true;
    }
}