using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;


class Slider
{
    Context z3;
    Solver slvr;

    static TextWriter twOut, twData;    // Output file

    const String TIME_OUT = "6000000";   // How long we want to search for the model?                            

    const int MAX_NUM_SOLUTION = 1;

    #region Constants
    const int NUM_OF_BUS = 14;
    const int MTU_ID = 58;

    const int ALPHA = 5;
    const int BETA = 3;

    const int MAX_NUM_PATH = 10;
    const int MAX_PATH_LEN = 20;

    const int MIN_ALT_PATH = 0;
    #endregion

    #region SMT Variables

    // SDNSynth vars
    BoolExpr[,] PhyLink;

    IntExpr[,] LinkBandwidth;

    IntExpr[] DeviceIsIED;
    IntExpr[] DeviceIsRTU;
    IntExpr[] DeviceIsRouter;

    BoolExpr[] RouterIsSDN;
    IntExpr[] RouterIsSDNCount;
    IntExpr[] PhyNewLinkCount;

    //IntExpr Alpha;
    //IntExpr Beta;

    // Jaka Test
    //IntExpr x;
    //IntExpr y;

    #endregion

    #region Input Variables

    int nIed;
    int nRtu;
    int nRouter;
    int nLinks;
    int[,] links;
    int[,] linkBandwidths;
    int nNewLinks;

    int[] iedData;

    int nThreatVectors;
    int[,] threatVectors;
    int nSdnRouter;
    int nSdnRouterCost;
    int nLinkCost;
    int budget;
    int[] routerIDs;

    int nVlan;
    int[,] vlans;
    int expectedVlanPer;

    #endregion

    public class SrcDestPair
    {
        public int src;
        public int dest;
        public int pathLen;
        public int[] pathLinks = new int[MAX_PATH_LEN];
        public int[] pathBandwidths = new int[MAX_PATH_LEN];
    }

    SrcDestPair[] linkSrcDest;
    SrcDestPair[] linkSrcDest2;

    #region To search (possible) paths for a flow

    int nPath;
    int pathLen;
    int[] path = new int[MAX_PATH_LEN];
    int[] pathLinkBandwidth = new int[MAX_PATH_LEN];
    int[] altPath = new int[MAX_PATH_LEN];
    int pathIDForIED = 0;
    int[,] allPathsForIED = new int[MAX_NUM_PATH, MAX_PATH_LEN]; // TODO: Change the first index.

    Dictionary<int, int[,]> mapSrcToAllPaths = new Dictionary<int, int[,]>();
    //int[] effectiveAltPathIDs = new int[MAX_NUM_PATH];
    List<int> effectiveAltPathIDs = new List<int>(MAX_NUM_PATH);
    Dictionary<int, int[]> mapSrcToAltPaths = new Dictionary<int, int[]>();

    // Find the path
    void findPath(int src, int dest, int len)
    {
        int i, j;

        if (links[path[len - 1], dest] >= 0) // Destination is reached
        {
            nPath++;
            path[len] = dest;
            pathLinkBandwidth[len - 1] = linkBandwidths[path[len - 1], path[len]];
            pathLen = len;

            // Clear up the rest of the path.
            for (int l = len+1; l < MAX_PATH_LEN; l++)
                path[l] = 0;
            
            //// Set up interServerThroughput
            //int min = Int32.MaxValue;
            //for (int k = 0; k < len; k++)
            //{
            //    if (min > linkBandwidths[path[k], path[k + 1]])
            //    {
            //        min = linkBandwidths[path[k], path[k + 1]];
            //    }
            //}
            //interServerThroughput[src, dest] = min; 
        }
        else // Looking for other paths
        {
            for (i = nIed+1; i < (nIed + nRtu + nRouter+1); i++)
            {
                for (j = 0; j < len; j++)
                {
                    if (path[j] == i)
                        break;
                }

                if ((j == len) && (links[path[len - 1], i] >= 0/* || (links[path[len - 1], i] == -100)*/))
                {
                    path[len] = i;
                    pathLinkBandwidth[len - 1] = linkBandwidths[path[len - 1], path[len]];
                    pathLen = len;
                    findPath(src, dest, len + 1);
                }
            }
        }
    }

    // Find the path
    void findAltPath(int src, int dest, int len)
    {
        int i, j;

        if (links[altPath[len - 1], dest] >= 0) // Destination is reached
        {
            nPath++;
            altPath[len] = dest;
            pathLen = len;

            // Clear up the rest of the path.
            for (int l = len + 1; l < MAX_PATH_LEN; l++)
                altPath[l] = 0;

            bool duplicatePath = true;
            for (int a = 0; a < allPathsForIED.GetLength(0); a++)
            {
                duplicatePath = true;
                for (int t = 0; t < altPath.Length; t++)
                {
                    if (allPathsForIED[a,t] != altPath[t])
                    {
                        duplicatePath = false;
                        break;
                    }
                }

                if (duplicatePath)
                    break;
            }

            if (!duplicatePath)
            {
                for (int l = 0; l < altPath.Length; l++)
                {
                    allPathsForIED[pathIDForIED, l] = altPath[l];
                }
                pathIDForIED++; // TODO: Reset this when all paths found for one IED.
            }
        }
        else // Looking for other paths
        {
            for (i = nIed + 1; i < (nIed + nRtu + nRouter + 1); i++)
            {
                for (j = 0; j < len; j++)
                {
                    if (altPath[j] == i)
                        break;
                }

                if ((j == len) && ((links[altPath[len - 1], i] >= 0)/* || (links[altPath[len - 1], i] == -100)*/))
                {
                    altPath[len] = i;
                    pathLen = len;
                    findAltPath(src, dest, len + 1);
                }
            }
        }
    }

    // Get the path from src to dest
    void getPath(int src, int dest)
    {
        path[0] = src;
        findPath(src, dest, 1);
    }

    bool isEffectiveAltPath(int iedID, int[] arr1, int[] arr2)
    {
        int sameNodeCount = 0;
        for (int i = 0; i < arr1.Length; i++)
        {
            for (int j = 0; j < arr2.Length; j++)
            {
                if (arr1[i] != 0 && arr1[i] == arr2[j])
                    sameNodeCount++;
            }
        }

        if (sameNodeCount > 0 && (sameNodeCount / ((arr1.Length + arr2.Length) / 2) < 0.5))
            return true;

        return false;
    }
    void getAltPaths(int src, int dest)
    {
        altPath[0] = src;

        for (int p = 0; p < MAX_NUM_PATH; p++)
        {
            findAltPath(src, dest, 1);
        }

        int[,] temp = new int[MAX_NUM_PATH, MAX_PATH_LEN];
        temp = allPathsForIED.Clone() as int[,];
        mapSrcToAllPaths.Add(src, temp);
        pathIDForIED = 0; // TODO: Reset this when all paths found for one IED.
        //allPathsForIED.Initialize();
        Array.Clear(allPathsForIED, 0, allPathsForIED.Length); // Zero out (initialize) the array.
    }
    #endregion

    bool bSat;  // If there is a satisfiable model?
    static String fIn = String.Format("Input_{0}.txt", NUM_OF_BUS);

    // Read input from the file
    void readInput()
    {
        String str;
        String line;
        String[] words;

        char[] delims = { ' ', ',', '\t' };

        try
        {
            ////////// Preliminary Initialization //////////            
            //Zero = z3.MkInt(0);
            //One = z3.MkInt(1);

            System.IO.StreamReader file = new System.IO.StreamReader(fIn);

            #region Read the number of devices
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Num Devices");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 3)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Num Devices");
                }

                nIed = Convert.ToInt32(words[0]);
                nRtu = Convert.ToInt32(words[1]);
                nRouter = Convert.ToInt32(words[2]);

                iedData = new int[nIed+1];
                links = new int[nIed + nRtu + nRouter + 1 + 1, nIed + nRtu + nRouter + 1 + 1]; // Assuming 1 MTU.
                linkBandwidths = new int[nIed + nRtu + nRouter + 1 + 1, nIed + nRtu + nRouter + 1 + 1];
                PhyLink = new BoolExpr[nIed + nRtu + nRouter + 1 + 1, nIed + nRtu + nRouter + 1 + 1];

                RouterIsSDN = new BoolExpr[nRouter + 1];
                RouterIsSDNCount = new IntExpr[nRouter + 1];

                linkSrcDest = new SrcDestPair[nIed + 1];
                linkSrcDest2 = new SrcDestPair[nIed + 1];

                break;
            }
            #endregion

            #region Read the data generated by IEDs
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: IED Data");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != nIed)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: IED Data");
                }

                for (int d = 1; d <= nIed; d++)
                {
                    iedData[d] = Convert.ToInt32(words[d-1]);
                }

                break;
            }
            #endregion

            #region Read the number of links in the topology
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Num Server");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Num Server");
                }

                nLinks = Convert.ToInt32(words[0]);
                break;
            }
            #endregion

            #region Read the available links
            // Initialize all link IDs as -1
            for (int i = 1; i <= (nIed + nRtu + nRouter + 1); i++)
            {
                for (int j = 1; j <= (nIed + nRtu + nRouter + 1); j++)
                {
                    links[i, j] = -1;
                    linkBandwidths[i, j] = -1;
                }
            }

            for (int i = 0; i <= nIed + nRtu + nRouter + 1; i++)
            {
                for (int j = 0; j <= nIed + nRtu + nRouter + 1; j++)
                {
                    str = String.Format("PhyLink_{0}_{1}", i, j);
                    PhyLink[i, j] = (BoolExpr)z3.MkConst(str, z3.BoolSort);
                }
            }
                
            for (int i = 1; i <= nLinks; i++)
            {
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: Links");
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    words = line.Split(delims);
                    if (words.Length != 3)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: Links");
                    }

                    // Assign link bandwidths
                    linkBandwidths[Convert.ToInt32(words[0]), Convert.ToInt32(words[1])] = Convert.ToInt32(words[2]);
                    linkBandwidths[Convert.ToInt32(words[1]), Convert.ToInt32(words[0])] = Convert.ToInt32(words[2]);

                    links[Convert.ToInt32(words[0]), Convert.ToInt32(words[1])] = i;
                    links[Convert.ToInt32(words[1]), Convert.ToInt32(words[0])] = i;

                    break;
                }
            }

            #endregion

            #region Read the number of potential new links in the topology
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: New Link");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: New Link");
                }

                nNewLinks = Convert.ToInt32(words[0]);
                PhyNewLinkCount = new IntExpr[nNewLinks + 1];

                break;
            }
            #endregion

            #region Read the potential links and put -100 in their places.

            for (int i = 1; i <= nNewLinks; i++)
            {
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: Links");
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    words = line.Split(delims);
                    if (words.Length != 3)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: Links");
                    }

                    
                    links[Convert.ToInt32(words[0]), Convert.ToInt32(words[1])] = -100;
                    links[Convert.ToInt32(words[1]), Convert.ToInt32(words[0])] = -100;

                    break;
                }
            }

            #endregion

            #region Read Number of Threat vectors
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: #Threat Vectors");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: #Threat Vectors");
                }

                nThreatVectors = Convert.ToInt32(words[0]);
                threatVectors = new int[nThreatVectors+1, nIed+1];

                // Clear the array.
                for (int i = 1; i <= nThreatVectors; i++)
                    for (int j = 1; j <= nIed; j++)
                    {
                        threatVectors[i, j] = 0;
                    }

                break;
            }
            #endregion

            #region Read Threat vectors
            while (true)
            {
                for (int i = 1; i <= nThreatVectors; i++)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: #Threat Vectors");
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    words = line.Split(delims);
                    int numWords = words.Length;
                    //int[] iedIDs = new int[numWords];

                    for (int t = 0; t < numWords; t++)
                    {
                        threatVectors[i, Convert.ToInt32(words[t])] = 1;
                    }
                }

                break;
            }
            #endregion

            #region Read Current SDN router IDs
            //TODO:
            #endregion

            #region Read Available SDN Routers
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: #SDN Router");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: #SDN Router");
                }

                nSdnRouter = Convert.ToInt32(words[0]);

                break;
            }
            #endregion

            #region Read cost of SDN Routers
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: SDN Router cost");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: SDN Router cost");
                }

                nSdnRouterCost = Convert.ToInt32(words[0]);

                break;
            }
            #endregion

            #region Read avg cost of link set up
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Link Cost");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Link Cost");
                }

                nLinkCost = Convert.ToInt32(words[0]);

                break;
            }
            #endregion

            #region Read budget
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Budget");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Budget");
                }

                budget = Convert.ToInt32(words[0]);

                break;
            }
            #endregion

            #region Read Number of VLANs
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: #VLANs");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: #VLANs");
                }

                nVlan = Convert.ToInt32(words[0]);
                vlans = new int[nVlan + 1, nIed + 1];

                for (int i = 1; i <= nVlan; i++)
                    for (int j = 1; j <= nIed; j++)
                    {
                        vlans[i, j] = 0;
                    }

                break;
            }
            #endregion

            #region Read VLANs
            while (true)
            {
                for (int i = 1; i <= nVlan; i++)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: #VLANs");
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    words = line.Split(delims);
                    int numWords = words.Length;
                    //int[] iedIDs = new int[numWords];

                    for (int t = 0; t < numWords; t++)
                    {
                        vlans[i, Convert.ToInt32(words[t])] = 1;
                    }
                }

                break;
            }
            #endregion

            #region Read expected VLAN percentage
            while (true)
            {
                if ((line = file.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Expected VLAN percentage");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                words = line.Split(delims);
                if (words.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Expected VLAN percentage");
                }

                expectedVlanPer = Convert.ToInt32(words[0]);

                break;
            }
            #endregion
            file.Close();

            
        }
        catch (Exception exp)
        {
            throw exp;
        }
    }

    IntExpr[] termsTotalVMPackProcRate; ///////

    // Modeling the system
    void Model()
    {
        try
        {
            //Context.ToggleWarningMessages(true);            

            Console.Write("Z3 Major Version: ");
            Console.WriteLine(Microsoft.Z3.Version.Major.ToString());
            Console.Write("Z3 Full Version: ");
            Console.WriteLine(Microsoft.Z3.Version.ToString());

            Dictionary<string, string> cfg = new Dictionary<string, string>() {
                    { "MODEL", "true"}      
                    //{ "PULL_NESTED_QUANTIFIERS", "true"},
                    //{ "smt.soft_timeout", TIME_OUT}
                };


            using (z3 = new Context(cfg))
            {
                slvr = z3.MkSolver();

                readInput();


                #region test code

                //x = (IntExpr)z3.MkConst("x", z3.IntSort);
                //y = (IntExpr)z3.MkConst("y", z3.IntSort);

                ////x + y = 5
                //IntExpr Five = z3.MkInt(5);
                //IntExpr[] terms1 = new IntExpr[2];
                //terms1[0] = x;
                //terms1[1] = y;

                //BoolExpr body1 = z3.MkEq(z3.MkAdd(terms1), Five);
                //slvr.Assert(body1);
                //twOut.WriteLine("{0}", body1.ToString());

                ////y + 1 = x
                //IntExpr One = z3.MkInt(1);
                //IntExpr[] terms2 = new IntExpr[2];
                //terms2[0] = x;
                //terms2[1] = y;

                //BoolExpr body2 = z3.MkEq(z3.MkSub(x, y), One);
                //slvr.Assert(body2);
                //twOut.WriteLine("{0}", body2.ToString());

                #endregion

                #region Model

                string str;
                IntExpr Zero = z3.MkInt(0);
                IntExpr One = z3.MkInt(1);

                #region Initialization
                for (int i = 0; i < nRouter + 1; i++)
                {
                    str = String.Format("RouterIsSDN_{0}", i);
                    RouterIsSDN[i] = (BoolExpr)z3.MkConst(str, z3.BoolSort);

                    string str1 = String.Format("RouterIsSDNCount_{0}", i);
                    RouterIsSDNCount[i] = (IntExpr)z3.MkConst(str1, z3.IntSort);
                }

                for (int l = 0; l < nNewLinks + 1; l++)
                {
                    string str1 = String.Format("PhyNewLinkCount_{0}", l);
                    PhyNewLinkCount[l] = (IntExpr)z3.MkConst(str1, z3.IntSort);
                }
                #endregion

                #region Find path for each IED to the MTU
                // Find path for each server to the others
                for (int i = 1; i <= nIed; i++)
                {
                    nPath = 0;
                    pathLen = 0;

                    int j = MTU_ID;
                    Array.Clear(path, 0, MAX_PATH_LEN);
                    Array.Clear(pathLinkBandwidth, 0, MAX_PATH_LEN);
                    getPath(i, j);
                    SrcDestPair obj = new SrcDestPair();
                    obj.src = i;
                    obj.dest = j;
                    pathLinkBandwidth.CopyTo(obj.pathBandwidths, 0);
                    path.CopyTo(obj.pathLinks, 0);
                    obj.pathLen = pathLen;
                    linkSrcDest[i] = obj;
                }
                #endregion

                #region Each link on the path should be wide enough to carry the data from IED
                for (int i = 1; i <= nIed; i++)
                {
                    
                    SrcDestPair obj = linkSrcDest[i];
                    for (int l = 0; l < obj.pathLen; l++)
                    {
                        int linkBandwidth = obj.pathBandwidths[l];
                        // Assert that link bandwidth is greater than the data generated by IED.
                        // In that case, we'll not read the bandwidth of each link from input file.
                        // Or we might keep them in input file and assert that these links have const values.
                        // The bandwidth is SMT variable.
                        BoolExpr body = z3.MkGe(z3.MkInt(linkBandwidth), z3.MkInt(iedData[i]));
                        slvr.Assert(body);
                    }

                }
                #endregion

                #region Make sure that the available links are up, and potential new links are up too.

                for (int i = 1; i <= (nIed + nRtu + nRouter + 1); i++)
                {
                    for (int j = 1; j <= (nIed + nRtu + nRouter + 1); j++)
                    {
                        if ((links[i, j] > 0 && linkBandwidths[i, j] > 0) || links[i, j] == -100)
                            slvr.Assert(PhyLink[i,j]);
                        else
                            slvr.Assert(z3.MkNot(PhyLink[i, j]));
                    }
                }

                #endregion

                #region The total cost of new links and SDN routers should not exceed the available budget

                for (int i = 0; i < nRouter+1; i++)
                {
                    slvr.Assert(z3.MkImplies(RouterIsSDN[i], z3.MkEq(RouterIsSDNCount[i], One)));
                    slvr.Assert(z3.MkImplies(z3.MkNot(RouterIsSDN[i]), z3.MkEq(RouterIsSDNCount[i], Zero)));
                }

                int newLinkIndex = 0;
                for (int i = 1; i <= (nIed + nRtu + nRouter + 1); i++)
                {
                    for (int j = 1; j <= (nIed + nRtu + nRouter + 1); j++)
                    {
                        if (links[i, j] == -100)
                        {
                            slvr.Assert(z3.MkImplies(PhyLink[i, j], z3.MkEq(PhyNewLinkCount[newLinkIndex], One)));
                            slvr.Assert(z3.MkImplies(z3.MkNot(PhyLink[i, j]), z3.MkEq(PhyNewLinkCount[newLinkIndex], Zero)));
                            newLinkIndex++;
                        }

                        if (newLinkIndex > nNewLinks)
                            break;
                    }

                    if (newLinkIndex > nNewLinks)
                        break;
                }

                BoolExpr body1 = z3.MkGe(z3.MkInt(budget), 
                                 z3.MkAdd(z3.MkMul(z3.MkInt(nSdnRouterCost), z3.MkAdd(RouterIsSDNCount)), 
                                          z3.MkMul(z3.MkInt(nLinkCost), z3.MkAdd(PhyNewLinkCount))));

                slvr.Assert(body1);

                slvr.Assert(z3.MkLe(z3.MkAdd(RouterIsSDNCount), z3.MkInt(nSdnRouter)));
                //slvr.Assert(z3.MkLe(z3.MkAdd(PhyNewLinkCount), z3.MkInt(nNewLinks)));

                slvr.Assert(z3.MkNot(z3.MkEq(z3.MkAdd(RouterIsSDNCount), Zero)));
                slvr.Assert(z3.MkNot(z3.MkEq(z3.MkAdd(PhyNewLinkCount), Zero)));

                #endregion

                #region For critical devices, there should be alternative paths, so that data can be sent successfully

                // Find alternate paths for each server to the others
                for (int i = 1; i <= nIed; i++)
                {
                    nPath = 0;
                    pathLen = 0;

                    int j = MTU_ID;
                    Array.Clear(altPath, 0, MAX_PATH_LEN);
                    getAltPaths(i, j);
                    SrcDestPair obj2 = new SrcDestPair();
                    obj2.src = i;
                    obj2.dest = j;
                    obj2.pathLen = pathLen;
                    linkSrcDest2[i] = obj2;
                }

                for (int i = 1; i <= nIed; i++)
                {
                    int[,] allPaths = new int[MAX_NUM_PATH, MAX_PATH_LEN];
                    mapSrcToAllPaths.TryGetValue(i, out allPaths);

                    if (allPaths != null)
                    {
                        for (int p = 0; p < allPaths.GetLength(0); p++)
                        {
                            bool effectiveAltPath = true;

                            int[] path1 = new int[MAX_PATH_LEN];
                            for (int j = 0; j < MAX_PATH_LEN; j++)
                            {
                                path1[j] = allPaths[p, j];
                            }

                            for (int e = 0; e < effectiveAltPathIDs.Count; e++)
                            {
                                int[] path2 = new int[MAX_PATH_LEN];
                                for (int k = 0; k < MAX_PATH_LEN; k++)
                                {
                                    path2[k] = allPaths[effectiveAltPathIDs[e],k];
                                }

                                if (!isEffectiveAltPath(i, path1, path2))
                                    effectiveAltPath = false;
                            }

                            if (effectiveAltPath)
                                effectiveAltPathIDs.Add(p);
                        }
                    }

                    int[] effectiveAltPathIDsArr = effectiveAltPathIDs.ToArray();
                    mapSrcToAltPaths.Add(i, effectiveAltPathIDsArr);

                    effectiveAltPathIDs.Clear();
                }

                for (int t = 1; t <= nThreatVectors; t++)
                {
                    for (int i = 1; i <= nIed; i++)
                    {
                        if (threatVectors[t, i] == 1)
                        {
                            int[] effAltPathIDsArr = new int[MAX_NUM_PATH];
                            mapSrcToAltPaths.TryGetValue(i, out effAltPathIDsArr);

                            if (effAltPathIDsArr != null)
                            {
                                int numEffectiveAltPaths = 0;
                                effAltPathIDsArr.GetLength(numEffectiveAltPaths);

                                slvr.Assert(z3.MkGe(z3.MkInt(numEffectiveAltPaths), z3.MkInt(MIN_ALT_PATH)));

                                // At least one IED in each attack vector should have alternate paths.
                                // We chose one.
                                break;
                            }
                        }
                    }
                }

                #endregion

                #region SDN switches should be deployed on the alternate paths for devices in threat vectors

                for (int t = 1; t <= nThreatVectors; t++)
                {
                    for (int i = 1; i <= nIed; i++)
                    {
                        if (threatVectors[t, i] == 1)
                        {
                            int[] effAltPathIDsArr = new int[MAX_NUM_PATH];
                            mapSrcToAltPaths.TryGetValue(i, out effAltPathIDsArr);

                            if (effAltPathIDsArr != null)
                            {
                                int[,] allPaths = new int[MAX_NUM_PATH, MAX_PATH_LEN];
                                mapSrcToAllPaths.TryGetValue(i, out allPaths);

                                for (int j = 0; j < effAltPathIDsArr.Length; j++)
                                {
                                    for (int k = j + 1; k < effAltPathIDsArr.Length; k++)
                                    {
                                        int effAltPathID1 = effAltPathIDsArr[j];
                                        int effAltPathID2 = effAltPathIDsArr[k];

                                        if (allPaths != null)
                                        {
                                            int[] path1 = new int[MAX_PATH_LEN];
                                            int[] path2 = new int[MAX_PATH_LEN];

                                            for (int l = 0; l < MAX_PATH_LEN; l++)
                                            {
                                                path1[l] = allPaths[effAltPathID1, l];
                                                path2[l] = allPaths[effAltPathID2, l];
                                            }

                                            bool bFoundFork = false;
                                            for (int m = 0; m < MAX_PATH_LEN; m++)
                                            {
                                                if (!bFoundFork && path1[m] != path2[m])
                                                {
                                                    bFoundFork = true;
                                                    int switchOnlyID = path1[m - 1] - (nIed + nRtu);
                                                    slvr.Assert(RouterIsSDN[switchOnlyID]);
                                                    //break;
                                                }

                                                if (bFoundFork && (path1[m] == path2[m]) && (path1[m] != 0) && (path2[m] != 0))
                                                {
                                                    // Assert SDN switch at next join.
                                                    int switchOnlyID = path1[m - 1] - (nIed + nRtu);
                                                    slvr.Assert(RouterIsSDN[switchOnlyID]);
                                                    break;
                                                }
                                            }

                                            #region The effective alternate paths from MTU to the IED should also have SDN switches on them
                                            int[] revPath1 = new int[MAX_PATH_LEN];
                                            //path1.CopyTo(revPath1, 0);
                                            //Array.Reverse(revPath1); // TODO: Need to reverse manually, and exclude the preceding zeros

                                            int jj = 0;
                                            for (int ii = MAX_PATH_LEN - 1; ii >= 0; ii--)
                                            {
                                                if (path1[ii] > 0)
                                                {
                                                    revPath1[jj] = path1[ii];
                                                    jj++;
                                                }
                                            }

                                            int[] revPath2 = new int[MAX_PATH_LEN];
                                            //path2.CopyTo(revPath2, 0);
                                            //Array.Reverse(revPath2);

                                            int jjj = 0;
                                            for (int iii = MAX_PATH_LEN - 1; iii >= 0; iii--)
                                            {
                                                if (path2[iii] > 0)
                                                {
                                                    revPath2[jjj] = path2[iii];
                                                    jjj++;
                                                }
                                            }

                                            for (int m = 0; m < MAX_PATH_LEN; m++)
                                            {
                                                if ((revPath1[m] != revPath2[m]) && (m > 1))
                                                {
                                                    int switchOnlyID = revPath1[m - 1] - (nIed + nRtu);
                                                    slvr.Assert(RouterIsSDN[switchOnlyID]);
                                                    break;
                                                }
                                            }
                                            #endregion
                                        }
                                    }
                                }
                            }
                            break;
                        }
                    }
                }


                #endregion

                #region VLANs should be created by SDN switches according to the expectation

                // For each threat vector, the adjacent switch of the IEDs in the VLAN should be SDN enabled.

                for (int t = 1; t <= nThreatVectors; t++)
                {
                    for (int i = 1; i <= nIed; i++)
                    {
                        bool bNeedsConfig = false;
                        int adjacentSwitchID = 0;

                        if (threatVectors[t, i] == 1)
                        {
                            bNeedsConfig = true;
                            // Find the adjacent switch and make sure this is SDN eanbled.
                            SrcDestPair obj = linkSrcDest[i];
                            if (obj.pathLinks.Length > 1)
                                adjacentSwitchID = obj.pathLinks[1];
                        }

                        if (bNeedsConfig && adjacentSwitchID > (nIed + nRtu))
                        {
                            int switchOnlyID = adjacentSwitchID - (nIed + nRtu);
                            slvr.Assert(RouterIsSDN[switchOnlyID]);
                        }
                    }
                }

                #endregion

                #region VLANs should be created by SDN switches according to the expectation

                // For each expected VLAN, the adjacent switch of all the IEDs in the VLAN should be SDN enabled.
                //for (int v = 1; v <= nVlan; v++)
                //{
                //    for (int i = 1; i <= nIed; i++)
                //    {
                //        bool bNeedsConfig = false;
                //        int adjacentSwitchID = 0;

                //        if (vlans[v, i] == 1)
                //        {
                //            bNeedsConfig = true;
                //            // Find the adjacent switch and make sure this is SDN eanbled.
                //            SrcDestPair obj = linkSrcDest[i];
                //            if (obj.pathLinks.Length > 1)
                //                adjacentSwitchID = obj.pathLinks[1];
                //        }

                //        if (bNeedsConfig)
                //        {
                //            int switchOnlyID = adjacentSwitchID - (nIed + nRtu);
                //            slvr.Assert(RouterIsSDN[switchOnlyID]);
                //        }
                //    }
                //}

                #endregion

                #endregion

                #region output

                Enumerate();
                
                #endregion                
            }
        }
        catch (Z3Exception ex)
        {
            Console.WriteLine("Z3 Managed Exception: " + ex.Message);
            Console.WriteLine("Stack trace: " + ex.StackTrace);
        }
        catch (Exception ex)
        {
            Console.WriteLine("Exception: " + ex.Message);
            Console.WriteLine("Stack trace: " + ex.StackTrace);
        }                        
    }

    // Enumerate the output 
    void Enumerate()
    {
        Model model = null;
        bSat = false;

        twData.WriteLine("***********************************");
        
        //
        // Print the solver
        //
        Console.WriteLine(slvr.ToString());

        #region Find solutions up to MAX_NUM_SOLUTION
        {
            int numSolution = 0;
            while (slvr.Check() == Status.SATISFIABLE)
            {
                bSat = true;

                model = slvr.Model;

                numSolution++;
                Console.WriteLine("{0}: We have a solution", numSolution);
                twOut.WriteLine("We have a solution");
                twData.WriteLine("{0}: We have a solution", numSolution);

                //twOut.Write(model.ToString());
                //twOut.WriteLine();

                twData.WriteLine(slvr.Statistics);
                Console.WriteLine(slvr.Statistics);
                twData.WriteLine();

                twData.WriteLine("Router ID\tIs Deployed?");
                bool bVal = false;
                int iVal = 0;
                for (int i = 1; i < nRouter+1; i++)
                {
                    bVal = Convert.ToBoolean(model.Eval(RouterIsSDN[i]).ToString());
                    iVal = Convert.ToInt32(model.Eval(RouterIsSDNCount[i]).ToString());
                    int iRouterID = i + nIed + nRtu;
                    string sVal = bVal ? "True" : "False";
                    twData.WriteLine("{0}\t{1}\t{2}", iRouterID, sVal, iVal);
                }

                twData.WriteLine("All existing and deployed links:");
                twData.WriteLine("Src\tDest\tStatus\tNew");
                bool bLinkIsUp = false;
                for (int i = 1; i <= (nIed + nRtu + nRouter + 1); i++)
                {
                    for (int j = 1; j <= (nIed + nRtu + nRouter + 1); j++)
                    {
                        bLinkIsUp = Convert.ToBoolean(model.Eval(PhyLink[i,j]).ToString());
                        string sLinkIsUp = bLinkIsUp ? "True" : "False";
                        bool bNewLinkUp = false;
                        if (bLinkIsUp && links[i, j] == -100)
                            bNewLinkUp = true;
                        string sNewLinkIsUp = bNewLinkUp ? "True" : "False";
                        if (bLinkIsUp)
                            twData.WriteLine("{0}\t{1}\t{2}\t{3}", i, j, sLinkIsUp, sNewLinkIsUp);
                    }
                }

                #region Jaka Test
                // Jaka Test
                //twData.WriteLine("Value of x: {0}", Convert.ToInt32(model.Eval(x).ToString()));
                //twData.WriteLine("Value of y: {0}", Convert.ToInt32(model.Eval(y).ToString()));
                #endregion

                model.Dispose();

                if (numSolution == MAX_NUM_SOLUTION)
                {

                    twData.WriteLine("***********************************");
                    twData.WriteLine();
                    break;
                }
                twData.WriteLine("..................................");

                
                Console.WriteLine("Searching for another solution...");
                twData.WriteLine("Searching for another solution...");
            }
        }
        #endregion        
        
        if (!bSat)
        {
            twData.WriteLine(slvr.UnsatCore);

            Console.WriteLine("We have no solution");
            twOut.WriteLine("We have no solution");

            twData.WriteLine("We have no solution");
        }
        
        //twData.WriteLine();
        //twData.Close();
    }

    // Main function
    static void Main(string[] args)
    {
        twOut = new StreamWriter("Output.txt", false);        

        Slider smart = new Slider();
        
        Stopwatch stopWatch = new Stopwatch();
        stopWatch.Start();

        twData = new StreamWriter("Data.txt", true);

        #region Program
        
        smart.Model();         
       
        #endregion

        stopWatch.Stop();
        
        Console.WriteLine("Required time: {0}", stopWatch.Elapsed.TotalMilliseconds);
        twOut.WriteLine("Required time: {0}\n\n", stopWatch.Elapsed.TotalMilliseconds);
        twData.WriteLine("Required time: {0}\n\n", stopWatch.Elapsed.TotalMilliseconds);

        twOut.Close();
        twData.Close();
    }
};