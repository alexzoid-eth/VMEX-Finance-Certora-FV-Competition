// SPDX-License-Identifier: agpl-3.0
pragma solidity 0.8.19;

import {AssetMappings} from "../../contracts/protocol/lendingpool/AssetMappings.sol";
import {DataTypes} from "../../contracts/protocol/libraries/types/DataTypes.sol";

/**
 * @title AssetMappings harness contract
 **/
contract AssetMappingsHarness is AssetMappings {

    function getRevisionHarness() external pure returns (uint256) {
        return getRevision();
    }

    function assetMappingsBorrowingEnabled(address asset) view external returns(bool) {
        return assetMappings[asset].borrowingEnabled;
    }
}