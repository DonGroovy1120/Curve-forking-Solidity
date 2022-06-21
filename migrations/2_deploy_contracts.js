const BEP20SphynxTokenImplementation = artifacts.require("BEP20SphynxTokenImplementation");
const BSCSphynxSwapAgentImpl = artifacts.require("BSCSphynxSwapAgentImpl");
const ETHSphynxSwapAgentImpl = artifacts.require("ETHSphynxSwapAgentImpl");

const ERC20SphynxABC = artifacts.require("ERC20SphynxABC");
const ERC20SphynxDEF = artifacts.require("ERC20SphynxDEF");
const ERC20SphynxEMPTYSYMBOL = artifacts.require("ERC20SphynxEMPTYSYMBOL");
const ERC20SphynxEMPTYNAME = artifacts.require("ERC20SphynxEMPTYNAME");

const Web3 = require('web3');
const web3 = new Web3(new Web3.providers.HttpProvider('http://localhost:8545'));

module.exports = function(deployer, network, accounts) {
    owner = accounts[0];
    proxyAdmin = accounts[1];
    bep20ProxyAdmin = accounts[0];
    deployer.then(async () => {
        await deployer.deploy(ERC20SphynxABC);
        await deployer.deploy(ERC20SphynxDEF);
        await deployer.deploy(ERC20SphynxEMPTYSYMBOL);
        await deployer.deploy(ERC20SphynxEMPTYNAME);
        await deployer.deploy(BEP20SphynxTokenImplementation);
        if ( network === 'bscTestnet') {
            await deployer.deploy(BSCSphynxSwapAgentImpl, BEP20SphynxTokenImplementation.address, "10000000000000000", bep20ProxyAdmin);
        } 
        if ( network === 'ethTestnet' || network === 'development') {
            await deployer.deploy(ETHSphynxSwapAgentImpl, "10000000");
        }
    });
};
