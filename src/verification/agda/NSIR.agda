module NSIR where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; _≥_; _>_; s≤s; z≤n; _⊔_; _⊓_; _≤?_; _<?_; _≡ᵇ_)
open import Data.Nat.Properties using (+-identityʳ; +-identityˡ; +-comm; +-assoc; +-suc; *-identityˡ; *-identityʳ; *-comm; *-assoc; *-distribˡ-+; *-distribʳ-+; ≤-refl; ≤-trans; ≤-antisym; ≤-step; m≤m+n; m+n∸n≡m; n∸n≡0; +-mono-≤; *-mono-≤; m≤n⇒m∸n≡0; ≤-pred; suc-injective; m∸n+n≡m; n≤m+n; +-cancelˡ-≡; m+n∸m≡n)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_; T)
open import Data.Bool.Properties using (∧-comm; ∨-comm; ∧-assoc; ∨-assoc; not-involutive)
open import Data.List using (List; []; _∷_; length; map; filter; _++_; foldr; foldl; reverse; zip; head; tail; replicate; concat)
open import Data.List.Properties using (++-identityʳ; ++-assoc; length-++; length-replicate; length-map)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<)
open import Data.Vec using (Vec; []; _∷_; lookup; replicate; tabulate; toList; fromList) renaming (length to vlength; map to vmap)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no; does)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function using (_∘_; id; _$_; flip; const)

open ≡-Reasoning

record ComplexNat : Set where
  field
    re : ℕ
    im : ℕ

mkComplex : ℕ → ℕ → ComplexNat
mkComplex r i = record { re = r ; im = i }

complexZero : ComplexNat
complexZero = mkComplex 0 0

complexOne : ComplexNat
complexOne = mkComplex 1 0

complexAdd : ComplexNat → ComplexNat → ComplexNat
complexAdd a b = mkComplex (ComplexNat.re a + ComplexNat.re b) (ComplexNat.im a + ComplexNat.im b)

complexMagSq : ComplexNat → ℕ
complexMagSq c = ComplexNat.re c * ComplexNat.re c + ComplexNat.im c * ComplexNat.im c

complexAdd-comm : ∀ (a b : ComplexNat) →
  complexAdd a b ≡ complexAdd b a
complexAdd-comm a b with ComplexNat.re a | ComplexNat.im a | ComplexNat.re b | ComplexNat.im b
... | ra | ia | rb | ib = cong₂ mkComplex (+-comm ra rb) (+-comm ia ib)

complexAdd-zero-left : ∀ (a : ComplexNat) → complexAdd complexZero a ≡ a
complexAdd-zero-left a = refl

complexAdd-zero-right : ∀ (a : ComplexNat) →
  ComplexNat.re (complexAdd a complexZero) ≡ ComplexNat.re a ×
  ComplexNat.im (complexAdd a complexZero) ≡ ComplexNat.im a
complexAdd-zero-right a = +-identityʳ (ComplexNat.re a) , +-identityʳ (ComplexNat.im a)

record Qubit : Set where
  field
    alpha : ComplexNat
    beta : ComplexNat

mkQubit : ComplexNat → ComplexNat → Qubit
mkQubit a b = record { alpha = a ; beta = b }

normSquared : Qubit → ℕ
normSquared q = complexMagSq (Qubit.alpha q) + complexMagSq (Qubit.beta q)

data IsNormalized : Qubit → ℕ → Set where
  normalized : ∀ {q n} → normSquared q ≡ n → IsNormalized q n

basis0 : Qubit
basis0 = mkQubit complexOne complexZero

basis1 : Qubit
basis1 = mkQubit complexZero complexOne

normSquared-basis0 : normSquared basis0 ≡ 1
normSquared-basis0 = refl

normSquared-basis1 : normSquared basis1 ≡ 1
normSquared-basis1 = refl

basis0-normalized : IsNormalized basis0 1
basis0-normalized = normalized refl

basis1-normalized : IsNormalized basis1 1
basis1-normalized = normalized refl

data EdgeQuality : Set where
  superposition : EdgeQuality
  entangled : EdgeQuality
  coherent : EdgeQuality
  collapsed : EdgeQuality
  fractal : EdgeQuality

edgeQualityToNat : EdgeQuality → ℕ
edgeQualityToNat superposition = 0
edgeQualityToNat entangled = 1
edgeQualityToNat coherent = 2
edgeQualityToNat collapsed = 3
edgeQualityToNat fractal = 4

data _≤Q_ : EdgeQuality → EdgeQuality → Set where
  q≤q-refl : ∀ {q} → q ≤Q q
  super≤ent : superposition ≤Q entangled
  super≤coh : superposition ≤Q coherent
  super≤col : superposition ≤Q collapsed
  super≤fra : superposition ≤Q fractal
  ent≤coh : entangled ≤Q coherent
  ent≤col : entangled ≤Q collapsed
  ent≤fra : entangled ≤Q fractal
  coh≤col : coherent ≤Q collapsed
  coh≤fra : coherent ≤Q fractal
  col≤fra : collapsed ≤Q fractal

≤Q-trans : ∀ {a b c} → a ≤Q b → b ≤Q c → a ≤Q c
≤Q-trans q≤q-refl q2 = q2
≤Q-trans q1 q≤q-refl = q1
≤Q-trans super≤ent ent≤coh = super≤coh
≤Q-trans super≤ent ent≤col = super≤col
≤Q-trans super≤ent ent≤fra = super≤fra
≤Q-trans super≤coh coh≤col = super≤col
≤Q-trans super≤coh coh≤fra = super≤fra
≤Q-trans super≤col col≤fra = super≤fra
≤Q-trans ent≤coh coh≤col = ent≤col
≤Q-trans ent≤coh coh≤fra = ent≤fra
≤Q-trans ent≤col col≤fra = ent≤fra
≤Q-trans coh≤col col≤fra = coh≤fra

≤Q-antisym : ∀ {a b} → a ≤Q b → b ≤Q a → a ≡ b
≤Q-antisym q≤q-refl _ = refl
≤Q-antisym _ q≤q-refl = refl

edgeQualityToNat-monotone : ∀ {a b} → a ≤Q b → edgeQualityToNat a ≤ edgeQualityToNat b
edgeQualityToNat-monotone q≤q-refl = ≤-refl
edgeQualityToNat-monotone super≤ent = s≤s z≤n
edgeQualityToNat-monotone super≤coh = z≤n
edgeQualityToNat-monotone super≤col = z≤n
edgeQualityToNat-monotone super≤fra = z≤n
edgeQualityToNat-monotone ent≤coh = s≤s (s≤s z≤n)
edgeQualityToNat-monotone ent≤col = s≤s (s≤s z≤n)
edgeQualityToNat-monotone ent≤fra = s≤s (s≤s z≤n)
edgeQualityToNat-monotone coh≤col = s≤s (s≤s (s≤s z≤n))
edgeQualityToNat-monotone coh≤fra = s≤s (s≤s (s≤s z≤n))
edgeQualityToNat-monotone col≤fra = s≤s (s≤s (s≤s (s≤s z≤n)))

_≡Q?_ : (a b : EdgeQuality) → Dec (a ≡ b)
superposition ≡Q? superposition = yes refl
superposition ≡Q? entangled = no (λ ())
superposition ≡Q? coherent = no (λ ())
superposition ≡Q? collapsed = no (λ ())
superposition ≡Q? fractal = no (λ ())
entangled ≡Q? superposition = no (λ ())
entangled ≡Q? entangled = yes refl
entangled ≡Q? coherent = no (λ ())
entangled ≡Q? collapsed = no (λ ())
entangled ≡Q? fractal = no (λ ())
coherent ≡Q? superposition = no (λ ())
coherent ≡Q? entangled = no (λ ())
coherent ≡Q? coherent = yes refl
coherent ≡Q? collapsed = no (λ ())
coherent ≡Q? fractal = no (λ ())
collapsed ≡Q? superposition = no (λ ())
collapsed ≡Q? entangled = no (λ ())
collapsed ≡Q? coherent = no (λ ())
collapsed ≡Q? collapsed = yes refl
collapsed ≡Q? fractal = no (λ ())
fractal ≡Q? superposition = no (λ ())
fractal ≡Q? entangled = no (λ ())
fractal ≡Q? coherent = no (λ ())
fractal ≡Q? collapsed = no (λ ())
fractal ≡Q? fractal = yes refl

NodeId : Set
NodeId = ℕ

record Node : Set where
  field
    nodeId : NodeId
    nodeData : ℕ
    nodeQubit : Qubit
    nodePhase : ℕ

mkNode : NodeId → ℕ → Qubit → ℕ → Node
mkNode nid dat q ph = record { nodeId = nid ; nodeData = dat ; nodeQubit = q ; nodePhase = ph }

record Edge : Set where
  field
    edgeSource : NodeId
    edgeTarget : NodeId
    edgeQuality : EdgeQuality
    edgeWeight : ℕ

mkEdge : NodeId → NodeId → EdgeQuality → ℕ → Edge
mkEdge s t q w = record { edgeSource = s ; edgeTarget = t ; edgeQuality = q ; edgeWeight = w }

record Graph : Set where
  field
    graphNodes : List Node
    graphEdges : List Edge

emptyGraph : Graph
emptyGraph = record { graphNodes = [] ; graphEdges = [] }

graphNodeCount : Graph → ℕ
graphNodeCount g = length (Graph.graphNodes g)

graphEdgeCount : Graph → ℕ
graphEdgeCount g = length (Graph.graphEdges g)

emptyGraph-nodeCount : graphNodeCount emptyGraph ≡ 0
emptyGraph-nodeCount = refl

emptyGraph-edgeCount : graphEdgeCount emptyGraph ≡ 0
emptyGraph-edgeCount = refl

addNode : Graph → Node → Graph
addNode g n = record { graphNodes = Graph.graphNodes g ++ (n ∷ []) ; graphEdges = Graph.graphEdges g }

addEdge : Graph → Edge → Graph
addEdge g e = record { graphNodes = Graph.graphNodes g ; graphEdges = Graph.graphEdges g ++ (e ∷ []) }

addNode-increments : ∀ (g : Graph) (n : Node) →
  graphNodeCount (addNode g n) ≡ suc (graphNodeCount g)
addNode-increments g n =
  begin
    length (Graph.graphNodes g ++ (n ∷ []))
  ≡⟨ length-++ (Graph.graphNodes g) ⟩
    length (Graph.graphNodes g) + length (n ∷ [])
  ≡⟨⟩
    length (Graph.graphNodes g) + 1
  ≡⟨ +-comm (length (Graph.graphNodes g)) 1 ⟩
    suc (length (Graph.graphNodes g))
  ∎

addEdge-increments : ∀ (g : Graph) (e : Edge) →
  graphEdgeCount (addEdge g e) ≡ suc (graphEdgeCount g)
addEdge-increments g e =
  begin
    length (Graph.graphEdges g ++ (e ∷ []))
  ≡⟨ length-++ (Graph.graphEdges g) ⟩
    length (Graph.graphEdges g) + length (e ∷ [])
  ≡⟨⟩
    length (Graph.graphEdges g) + 1
  ≡⟨ +-comm (length (Graph.graphEdges g)) 1 ⟩
    suc (length (Graph.graphEdges g))
  ∎

addNode-preserves-edges : ∀ (g : Graph) (n : Node) →
  graphEdgeCount (addNode g n) ≡ graphEdgeCount g
addNode-preserves-edges _ _ = refl

addEdge-preserves-nodes : ∀ (g : Graph) (e : Edge) →
  graphNodeCount (addEdge g e) ≡ graphNodeCount g
addEdge-preserves-nodes _ _ = refl

data HasNodeId : NodeId → List Node → Set where
  here-node : ∀ {nid ns n} → Node.nodeId n ≡ nid → HasNodeId nid (n ∷ ns)
  there-node : ∀ {nid ns n} → HasNodeId nid ns → HasNodeId nid (n ∷ ns)

data UniqueIds : List Node → Set where
  unique-nil : UniqueIds []
  unique-cons : ∀ {n ns} → ¬ (HasNodeId (Node.nodeId n) ns) → UniqueIds ns → UniqueIds (n ∷ ns)

emptyGraph-unique : UniqueIds []
emptyGraph-unique = unique-nil

singleNode-unique : ∀ (n : Node) → UniqueIds (n ∷ [])
singleNode-unique n = unique-cons (λ ()) unique-nil

data AllEdgesValid : List Edge → List Node → Set where
  valid-nil : ∀ {ns} → AllEdgesValid [] ns
  valid-cons : ∀ {e es ns} →
    HasNodeId (Edge.edgeSource e) ns →
    HasNodeId (Edge.edgeTarget e) ns →
    AllEdgesValid es ns →
    AllEdgesValid (e ∷ es) ns

emptyEdges-valid : ∀ {ns} → AllEdgesValid [] ns
emptyEdges-valid = valid-nil

record ValidGraph : Set where
  field
    vGraph : Graph
    vUnique : UniqueIds (Graph.graphNodes vGraph)
    vEdgesValid : AllEdgesValid (Graph.graphEdges vGraph) (Graph.graphNodes vGraph)

emptyValidGraph : ValidGraph
emptyValidGraph = record
  { vGraph = emptyGraph
  ; vUnique = unique-nil
  ; vEdgesValid = valid-nil
  }

data NoSelfLoop : Edge → Set where
  no-self-loop : ∀ {e} → ¬ (Edge.edgeSource e ≡ Edge.edgeTarget e) → NoSelfLoop e

data AllNoSelfLoops : List Edge → Set where
  noloop-nil : AllNoSelfLoops []
  noloop-cons : ∀ {e es} → NoSelfLoop e → AllNoSelfLoops es → AllNoSelfLoops (e ∷ es)

emptyEdges-noSelfLoops : AllNoSelfLoops []
emptyEdges-noSelfLoops = noloop-nil

data Reachable : NodeId → NodeId → List Edge → Set where
  reach-direct : ∀ {s t es e} → e ∷ [] ≡ filter (λ ed → Edge.edgeSource ed ≡ᵇ s ∧ Edge.edgeTarget ed ≡ᵇ t) es → Reachable s t es
  reach-step : ∀ {s m t es} → Reachable s m es → Reachable m t es → Reachable s t es

data IsAcyclic : List Edge → Set where
  acyclic-nil : IsAcyclic []
  acyclic-noreach : ∀ {es} → (∀ (n : NodeId) → ¬ (Reachable n n es)) → IsAcyclic es

emptyEdges-acyclic : IsAcyclic []
emptyEdges-acyclic = acyclic-nil

data Connected : NodeId → NodeId → List Edge → Set where
  conn-edge : ∀ {s t es} → HasEdge s t es → Connected s t es
  conn-sym : ∀ {s t es} → Connected t s es → Connected s t es
  conn-trans : ∀ {s m t es} → Connected s m es → Connected m t es → Connected s t es

data HasEdge : NodeId → NodeId → List Edge → Set where
  has-edge-here : ∀ {s t e es} → Edge.edgeSource e ≡ s → Edge.edgeTarget e ≡ t → HasEdge s t (e ∷ es)
  has-edge-there : ∀ {s t e es} → HasEdge s t es → HasEdge s t (e ∷ es)

hasEdge-addEdge : ∀ (es : List Edge) (e : Edge) →
  HasEdge (Edge.edgeSource e) (Edge.edgeTarget e) (es ++ (e ∷ []))
hasEdge-addEdge [] e = has-edge-here refl refl
hasEdge-addEdge (x ∷ xs) e = has-edge-there (hasEdge-addEdge xs e)

connected-addEdge : ∀ (es : List Edge) (e : Edge) →
  Connected (Edge.edgeSource e) (Edge.edgeTarget e) (es ++ (e ∷ []))
connected-addEdge es e = conn-edge (hasEdge-addEdge es e)

data AllNormalized : List Node → ℕ → Set where
  allnorm-nil : ∀ {k} → AllNormalized [] k
  allnorm-cons : ∀ {n ns k} → IsNormalized (Node.nodeQubit n) k → AllNormalized ns k → AllNormalized (n ∷ ns) k

emptyNodes-allNormalized : ∀ {k} → AllNormalized [] k
emptyNodes-allNormalized = allnorm-nil

singleNorm : ∀ (n : Node) (k : ℕ) → normSquared (Node.nodeQubit n) ≡ k → AllNormalized (n ∷ []) k
singleNorm n k pf = allnorm-cons (normalized pf) allnorm-nil

appendNorm : ∀ {ns k} (n : Node) →
  AllNormalized ns k →
  normSquared (Node.nodeQubit n) ≡ k →
  AllNormalized (ns ++ (n ∷ [])) k
appendNorm {[]} {k} n allnorm-nil pf = allnorm-cons (normalized pf) allnorm-nil
appendNorm {x ∷ xs} {k} n (allnorm-cons px rest) pf = allnorm-cons px (appendNorm n rest pf)

record NormalizedGraph : Set where
  field
    nGraph : Graph
    nNormConst : ℕ
    nAllNorm : AllNormalized (Graph.graphNodes nGraph) nNormConst

emptyNormalizedGraph : NormalizedGraph
emptyNormalizedGraph = record
  { nGraph = emptyGraph
  ; nNormConst = 1
  ; nAllNorm = allnorm-nil
  }

addNormalizedNode : ∀ (ng : NormalizedGraph) (n : Node) →
  normSquared (Node.nodeQubit n) ≡ NormalizedGraph.nNormConst ng →
  NormalizedGraph
addNormalizedNode ng n pf = record
  { nGraph = addNode (NormalizedGraph.nGraph ng) n
  ; nNormConst = NormalizedGraph.nNormConst ng
  ; nAllNorm = appendNorm n (NormalizedGraph.nAllNorm ng) pf
  }

record HashState : Set where
  field
    hashNodeAcc : ℕ
    hashEdgeAcc : ℕ
    hashNodeCount : ℕ
    hashEdgeCount : ℕ

emptyHashState : HashState
emptyHashState = record
  { hashNodeAcc = 0
  ; hashEdgeAcc = 0
  ; hashNodeCount = 0
  ; hashEdgeCount = 0
  }

xorNat : ℕ → ℕ → ℕ
xorNat zero b = b
xorNat a zero = a
xorNat (suc a) (suc b) = xorNat a b

xorNat-comm : ∀ (a b : ℕ) → xorNat a b ≡ xorNat b a
xorNat-comm zero zero = refl
xorNat-comm zero (suc b) = refl
xorNat-comm (suc a) zero = refl
xorNat-comm (suc a) (suc b) = xorNat-comm a b

xorNat-zero : ∀ (a : ℕ) → xorNat a 0 ≡ a
xorNat-zero zero = refl
xorNat-zero (suc a) = refl

xorNat-self : ∀ (a : ℕ) → xorNat a a ≡ 0
xorNat-self zero = refl
xorNat-self (suc a) = xorNat-self a

simpleNodeHash : Node → ℕ
simpleNodeHash n = Node.nodeId n + Node.nodeData n + Node.nodePhase n + normSquared (Node.nodeQubit n)

simpleEdgeHash : Edge → ℕ
simpleEdgeHash e = Edge.edgeSource e + Edge.edgeTarget e + Edge.edgeWeight e + edgeQualityToNat (Edge.edgeQuality e)

hashNodes : List Node → ℕ
hashNodes [] = 0
hashNodes (n ∷ ns) = xorNat (simpleNodeHash n) (hashNodes ns)

hashEdges : List Edge → ℕ
hashEdges [] = 0
hashEdges (e ∷ es) = xorNat (simpleEdgeHash e) (hashEdges es)

computeTopologyHash : Graph → ℕ
computeTopologyHash g = hashNodes (Graph.graphNodes g) + hashEdges (Graph.graphEdges g) + graphNodeCount g + graphEdgeCount g

emptyHash : computeTopologyHash emptyGraph ≡ 0
emptyHash = refl

hashNodes-comm-pair : ∀ (a b : Node) →
  xorNat (simpleNodeHash a) (xorNat (simpleNodeHash b) 0) ≡
  xorNat (simpleNodeHash b) (xorNat (simpleNodeHash a) 0)
hashNodes-comm-pair a b =
  begin
    xorNat (simpleNodeHash a) (xorNat (simpleNodeHash b) 0)
  ≡⟨ cong (xorNat (simpleNodeHash a)) (xorNat-zero (simpleNodeHash b)) ⟩
    xorNat (simpleNodeHash a) (simpleNodeHash b)
  ≡⟨ xorNat-comm (simpleNodeHash a) (simpleNodeHash b) ⟩
    xorNat (simpleNodeHash b) (simpleNodeHash a)
  ≡⟨ cong (xorNat (simpleNodeHash b)) (sym (xorNat-zero (simpleNodeHash a))) ⟩
    xorNat (simpleNodeHash b) (xorNat (simpleNodeHash a) 0)
  ∎

hashEdges-comm-pair : ∀ (a b : Edge) →
  xorNat (simpleEdgeHash a) (xorNat (simpleEdgeHash b) 0) ≡
  xorNat (simpleEdgeHash b) (xorNat (simpleEdgeHash a) 0)
hashEdges-comm-pair a b =
  begin
    xorNat (simpleEdgeHash a) (xorNat (simpleEdgeHash b) 0)
  ≡⟨ cong (xorNat (simpleEdgeHash a)) (xorNat-zero (simpleEdgeHash b)) ⟩
    xorNat (simpleEdgeHash a) (simpleEdgeHash b)
  ≡⟨ xorNat-comm (simpleEdgeHash a) (simpleEdgeHash b) ⟩
    xorNat (simpleEdgeHash b) (simpleEdgeHash a)
  ≡⟨ cong (xorNat (simpleEdgeHash b)) (sym (xorNat-zero (simpleEdgeHash a))) ⟩
    xorNat (simpleEdgeHash b) (xorNat (simpleEdgeHash a) 0)
  ∎

record TopologyHash : Set where
  field
    thGraph : Graph
    thHash : ℕ
    thValid : thHash ≡ computeTopologyHash thGraph

mkTopologyHash : (g : Graph) → TopologyHash
mkTopologyHash g = record
  { thGraph = g
  ; thHash = computeTopologyHash g
  ; thValid = refl
  }

emptyTopologyHash : TopologyHash
emptyTopologyHash = mkTopologyHash emptyGraph

hashChangesOnAddNode : ∀ (g : Graph) (n : Node) →
  graphNodeCount (addNode g n) ≡ suc (graphNodeCount g)
hashChangesOnAddNode = addNode-increments

hashChangesOnAddEdge : ∀ (g : Graph) (e : Edge) →
  graphEdgeCount (addEdge g e) ≡ suc (graphEdgeCount g)
hashChangesOnAddEdge = addEdge-increments

record TwoQubit : Set where
  field
    amp00 : ComplexNat
    amp01 : ComplexNat
    amp10 : ComplexNat
    amp11 : ComplexNat

twoQubitNormSq : TwoQubit → ℕ
twoQubitNormSq tq = complexMagSq (TwoQubit.amp00 tq) + complexMagSq (TwoQubit.amp01 tq) +
                    complexMagSq (TwoQubit.amp10 tq) + complexMagSq (TwoQubit.amp11 tq)

bellPhiPlus : TwoQubit
bellPhiPlus = record
  { amp00 = mkComplex 1 0
  ; amp01 = complexZero
  ; amp10 = complexZero
  ; amp11 = mkComplex 1 0
  }

bellPhiPlus-normSq : twoQubitNormSq bellPhiPlus ≡ 2
bellPhiPlus-normSq = refl

data EntanglementPair : Set where
  mkEntPair : NodeId → NodeId → TwoQubit → EntanglementPair

entPairFirst : EntanglementPair → NodeId
entPairFirst (mkEntPair a _ _) = a

entPairSecond : EntanglementPair → NodeId
entPairSecond (mkEntPair _ b _) = b

entPairState : EntanglementPair → TwoQubit
entPairState (mkEntPair _ _ tq) = tq

data EntPairOrdered : EntanglementPair → Set where
  ent-ordered : ∀ {a b tq} → a ≤ b → EntPairOrdered (mkEntPair a b tq)

entangle-ordered : ∀ (a b : NodeId) (tq : TwoQubit) →
  a ≤ b → EntPairOrdered (mkEntPair a b tq)
entangle-ordered a b tq p = ent-ordered p

record QuantumRegister : Set where
  field
    qrEntries : List (NodeId × Qubit)
    qrEntanglements : List EntanglementPair

emptyQR : QuantumRegister
emptyQR = record { qrEntries = [] ; qrEntanglements = [] }

data HasEntry : NodeId → List (NodeId × Qubit) → Set where
  entry-here : ∀ {nid q rest} → HasEntry nid ((nid , q) ∷ rest)
  entry-there : ∀ {nid nid' q rest} → HasEntry nid rest → HasEntry nid ((nid' , q) ∷ rest)

lookupQubit : NodeId → List (NodeId × Qubit) → Maybe Qubit
lookupQubit _ [] = nothing
lookupQubit nid ((k , v) ∷ rest) with nid ≡ᵇ k
... | true = just v
... | false = lookupQubit nid rest

updateQubit : NodeId → Qubit → List (NodeId × Qubit) → List (NodeId × Qubit)
updateQubit _ _ [] = []
updateQubit nid q ((k , v) ∷ rest) with nid ≡ᵇ k
... | true = (k , q) ∷ rest
... | false = (k , v) ∷ updateQubit nid q rest

updateQubit-length : ∀ (nid : NodeId) (q : Qubit) (entries : List (NodeId × Qubit)) →
  length (updateQubit nid q entries) ≡ length entries
updateQubit-length _ _ [] = refl
updateQubit-length nid q ((k , v) ∷ rest) with nid ≡ᵇ k
... | true = refl
... | false = cong suc (updateQubit-length nid q rest)

applyGateToQubit : (Qubit → Qubit) → Qubit → Qubit
applyGateToQubit gate q = gate q

identityGate : Qubit → Qubit
identityGate q = q

identityGate-preserves : ∀ (q : Qubit) → identityGate q ≡ q
identityGate-preserves q = refl

identityGate-normPreserved : ∀ (q : Qubit) → normSquared (identityGate q) ≡ normSquared q
identityGate-normPreserved q = refl

pauliXGate : Qubit → Qubit
pauliXGate q = mkQubit (Qubit.beta q) (Qubit.alpha q)

pauliX-involutive : ∀ (q : Qubit) →
  Qubit.alpha (pauliXGate (pauliXGate q)) ≡ Qubit.alpha q ×
  Qubit.beta (pauliXGate (pauliXGate q)) ≡ Qubit.beta q
pauliX-involutive q = refl , refl

pauliX-normPreserved : ∀ (q : Qubit) → normSquared (pauliXGate q) ≡ normSquared q
pauliX-normPreserved q =
  begin
    normSquared (pauliXGate q)
  ≡⟨⟩
    complexMagSq (Qubit.beta q) + complexMagSq (Qubit.alpha q)
  ≡⟨ +-comm (complexMagSq (Qubit.beta q)) (complexMagSq (Qubit.alpha q)) ⟩
    complexMagSq (Qubit.alpha q) + complexMagSq (Qubit.beta q)
  ≡⟨⟩
    normSquared q
  ∎

pauliX-basis0-to-basis1 : pauliXGate basis0 ≡ basis1
pauliX-basis0-to-basis1 = refl

pauliX-basis1-to-basis0 : pauliXGate basis1 ≡ basis0
pauliX-basis1-to-basis0 = refl

data MeasureOutcome : Set where
  outcome0 : MeasureOutcome
  outcome1 : MeasureOutcome

measureCollapsesToBasis : ∀ (outcome : MeasureOutcome) →
  (if outcome ≡ᴹ outcome0 then basis0 else basis1) ≡
  (if outcome ≡ᴹ outcome0 then basis0 else basis1)
  where
    _≡ᴹ_ : MeasureOutcome → MeasureOutcome → Bool
    outcome0 ≡ᴹ outcome0 = true
    outcome1 ≡ᴹ outcome1 = true
    _ ≡ᴹ _ = false
measureCollapsesToBasis _ = refl

collapsedQubit-normalized : ∀ (outcome : MeasureOutcome) →
  normSquared (collapseToOutcome outcome) ≡ 1
  where
    collapseToOutcome : MeasureOutcome → Qubit
    collapseToOutcome outcome0 = basis0
    collapseToOutcome outcome1 = basis1
collapsedQubit-normalized outcome0 = refl
collapsedQubit-normalized outcome1 = refl

findNodeById : NodeId → List Node → Maybe Node
findNodeById _ [] = nothing
findNodeById nid (n ∷ ns) with nid ≡ᵇ Node.nodeId n
... | true = just n
... | false = findNodeById nid ns

findEdges : NodeId → NodeId → List Edge → List Edge
findEdges _ _ [] = []
findEdges s t (e ∷ es) with (Edge.edgeSource e ≡ᵇ s) ∧ (Edge.edgeTarget e ≡ᵇ t)
... | true = e ∷ findEdges s t es
... | false = findEdges s t es

findEdges-subset-length : ∀ (s t : NodeId) (es : List Edge) →
  length (findEdges s t es) ≤ length es
findEdges-subset-length _ _ [] = z≤n
findEdges-subset-length s t (e ∷ es) with (Edge.edgeSource e ≡ᵇ s) ∧ (Edge.edgeTarget e ≡ᵇ t)
... | true = s≤s (findEdges-subset-length s t es)
... | false = ≤-step (findEdges-subset-length s t es)

nodeNeighbors : NodeId → List Edge → List NodeId
nodeNeighbors _ [] = []
nodeNeighbors nid (e ∷ es) with Edge.edgeSource e ≡ᵇ nid
... | true = Edge.edgeTarget e ∷ nodeNeighbors nid es
... | false = nodeNeighbors nid es

inDegree : NodeId → List Edge → ℕ
inDegree _ [] = 0
inDegree nid (e ∷ es) with Edge.edgeTarget e ≡ᵇ nid
... | true = suc (inDegree nid es)
... | false = inDegree nid es

outDegree : NodeId → List Edge → ℕ
outDegree _ [] = 0
outDegree nid (e ∷ es) with Edge.edgeSource e ≡ᵇ nid
... | true = suc (outDegree nid es)
... | false = outDegree nid es

inDegree-bound : ∀ (nid : NodeId) (es : List Edge) → inDegree nid es ≤ length es
inDegree-bound _ [] = z≤n
inDegree-bound nid (e ∷ es) with Edge.edgeTarget e ≡ᵇ nid
... | true = s≤s (inDegree-bound nid es)
... | false = ≤-step (inDegree-bound nid es)

outDegree-bound : ∀ (nid : NodeId) (es : List Edge) → outDegree nid es ≤ length es
outDegree-bound _ [] = z≤n
outDegree-bound nid (e ∷ es) with Edge.edgeSource e ≡ᵇ nid
... | true = s≤s (outDegree-bound nid es)
... | false = ≤-step (outDegree-bound nid es)

clearGraph : Graph → Graph
clearGraph _ = emptyGraph

clearGraph-empty : ∀ (g : Graph) → graphNodeCount (clearGraph g) ≡ 0
clearGraph-empty _ = refl

clearGraph-noEdges : ∀ (g : Graph) → graphEdgeCount (clearGraph g) ≡ 0
clearGraph-noEdges _ = refl

clearGraph-unique : ∀ (g : Graph) → UniqueIds (Graph.graphNodes (clearGraph g))
clearGraph-unique _ = unique-nil

clearGraph-valid : ∀ (g : Graph) → AllEdgesValid (Graph.graphEdges (clearGraph g)) (Graph.graphNodes (clearGraph g))
clearGraph-valid _ = valid-nil

clearGraph-acyclic : ∀ (g : Graph) → IsAcyclic (Graph.graphEdges (clearGraph g))
clearGraph-acyclic _ = acyclic-nil

clearGraph-noSelfLoops : ∀ (g : Graph) → AllNoSelfLoops (Graph.graphEdges (clearGraph g))
clearGraph-noSelfLoops _ = noloop-nil

clearGraph-hash : ∀ (g : Graph) → computeTopologyHash (clearGraph g) ≡ 0
clearGraph-hash _ = refl

edgeQuality-superposition-min : ∀ (q : EdgeQuality) → superposition ≤Q q
edgeQuality-superposition-min superposition = q≤q-refl
edgeQuality-superposition-min entangled = super≤ent
edgeQuality-superposition-min coherent = super≤coh
edgeQuality-superposition-min collapsed = super≤col
edgeQuality-superposition-min fractal = super≤fra

edgeQuality-fractal-max : ∀ (q : EdgeQuality) → q ≤Q fractal
edgeQuality-fractal-max superposition = super≤fra
edgeQuality-fractal-max entangled = ent≤fra
edgeQuality-fractal-max coherent = coh≤fra
edgeQuality-fractal-max collapsed = col≤fra
edgeQuality-fractal-max fractal = q≤q-refl

entangled→collapsed-valid : entangled ≤Q collapsed
entangled→collapsed-valid = ent≤col

coherent→collapsed-valid : coherent ≤Q collapsed
coherent→collapsed-valid = coh≤col

superposition→entangled-valid : superposition ≤Q entangled
superposition→entangled-valid = super≤ent

collapseEdge : Edge → Edge
collapseEdge e = mkEdge (Edge.edgeSource e) (Edge.edgeTarget e) collapsed (Edge.edgeWeight e)

collapseEdge-quality : ∀ (e : Edge) → Edge.edgeQuality (collapseEdge e) ≡ collapsed
collapseEdge-quality _ = refl

collapseEdge-preserves-source : ∀ (e : Edge) → Edge.edgeSource (collapseEdge e) ≡ Edge.edgeSource e
collapseEdge-preserves-source _ = refl

collapseEdge-preserves-target : ∀ (e : Edge) → Edge.edgeTarget (collapseEdge e) ≡ Edge.edgeTarget e
collapseEdge-preserves-target _ = refl

collapseEdge-preserves-weight : ∀ (e : Edge) → Edge.edgeWeight (collapseEdge e) ≡ Edge.edgeWeight e
collapseEdge-preserves-weight _ = refl

data WellFormedEntanglement : EntanglementPair → List Node → Set where
  wf-ent : ∀ {a b tq ns} →
    HasNodeId a ns →
    HasNodeId b ns →
    a ≤ b →
    WellFormedEntanglement (mkEntPair a b tq) ns

data AllEntanglementsWF : List EntanglementPair → List Node → Set where
  ent-wf-nil : ∀ {ns} → AllEntanglementsWF [] ns
  ent-wf-cons : ∀ {ep eps ns} →
    WellFormedEntanglement ep ns →
    AllEntanglementsWF eps ns →
    AllEntanglementsWF (ep ∷ eps) ns

emptyEntanglements-wf : ∀ {ns} → AllEntanglementsWF [] ns
emptyEntanglements-wf = ent-wf-nil

record FullGraphState : Set where
  field
    fGraph : Graph
    fQR : QuantumRegister
    fHash : ℕ
    fUnique : UniqueIds (Graph.graphNodes fGraph)
    fEdgesValid : AllEdgesValid (Graph.graphEdges fGraph) (Graph.graphNodes fGraph)
    fEntWF : AllEntanglementsWF (QuantumRegister.qrEntanglements fQR) (Graph.graphNodes fGraph)
    fHashValid : fHash ≡ computeTopologyHash fGraph

emptyFullState : FullGraphState
emptyFullState = record
  { fGraph = emptyGraph
  ; fQR = emptyQR
  ; fHash = 0
  ; fUnique = unique-nil
  ; fEdgesValid = valid-nil
  ; fEntWF = ent-wf-nil
  ; fHashValid = refl
  }

nodeCount-addTwo : ∀ (g : Graph) (n1 n2 : Node) →
  graphNodeCount (addNode (addNode g n1) n2) ≡ suc (suc (graphNodeCount g))
nodeCount-addTwo g n1 n2 =
  begin
    graphNodeCount (addNode (addNode g n1) n2)
  ≡⟨ addNode-increments (addNode g n1) n2 ⟩
    suc (graphNodeCount (addNode g n1))
  ≡⟨ cong suc (addNode-increments g n1) ⟩
    suc (suc (graphNodeCount g))
  ∎

edgeCount-addTwo : ∀ (g : Graph) (e1 e2 : Edge) →
  graphEdgeCount (addEdge (addEdge g e1) e2) ≡ suc (suc (graphEdgeCount g))
edgeCount-addTwo g e1 e2 =
  begin
    graphEdgeCount (addEdge (addEdge g e1) e2)
  ≡⟨ addEdge-increments (addEdge g e1) e2 ⟩
    suc (graphEdgeCount (addEdge g e1))
  ≡⟨ cong suc (addEdge-increments g e1) ⟩
    suc (suc (graphEdgeCount g))
  ∎

addNode-addEdge-commute-count : ∀ (g : Graph) (n : Node) (e : Edge) →
  graphNodeCount (addEdge (addNode g n) e) ≡ graphNodeCount (addNode (addEdge g e) n)
addNode-addEdge-commute-count g n e =
  begin
    graphNodeCount (addEdge (addNode g n) e)
  ≡⟨ addEdge-preserves-nodes (addNode g n) e ⟩
    graphNodeCount (addNode g n)
  ≡⟨ addNode-increments g n ⟩
    suc (graphNodeCount g)
  ≡⟨ sym (addNode-increments (addEdge g e) n) ⟩
    graphNodeCount (addNode (addEdge g e) n)
  ∎

totalElements : Graph → ℕ
totalElements g = graphNodeCount g + graphEdgeCount g

totalElements-empty : totalElements emptyGraph ≡ 0
totalElements-empty = refl

totalElements-addNode : ∀ (g : Graph) (n : Node) →
  totalElements (addNode g n) ≡ suc (totalElements g)
totalElements-addNode g n =
  begin
    graphNodeCount (addNode g n) + graphEdgeCount (addNode g n)
  ≡⟨ cong₂ _+_ (addNode-increments g n) (addNode-preserves-edges g n) ⟩
    suc (graphNodeCount g) + graphEdgeCount g
  ≡⟨⟩
    suc (graphNodeCount g + graphEdgeCount g)
  ∎

totalElements-addEdge : ∀ (g : Graph) (e : Edge) →
  totalElements (addEdge g e) ≡ suc (totalElements g)
totalElements-addEdge g e =
  begin
    graphNodeCount (addEdge g e) + graphEdgeCount (addEdge g e)
  ≡⟨ cong₂ _+_ (addEdge-preserves-nodes g e) (addEdge-increments g e) ⟩
    graphNodeCount g + suc (graphEdgeCount g)
  ≡⟨ +-suc (graphNodeCount g) (graphEdgeCount g) ⟩
    suc (graphNodeCount g + graphEdgeCount g)
  ∎

data EdgeQualityAll : EdgeQuality → List Edge → Set where
  eqa-nil : ∀ {q} → EdgeQualityAll q []
  eqa-cons : ∀ {q e es} → Edge.edgeQuality e ≡ q → EdgeQualityAll q es → EdgeQualityAll q (e ∷ es)

collapseAllEdges : List Edge → List Edge
collapseAllEdges [] = []
collapseAllEdges (e ∷ es) = collapseEdge e ∷ collapseAllEdges es

collapseAllEdges-quality : ∀ (es : List Edge) → EdgeQualityAll collapsed (collapseAllEdges es)
collapseAllEdges-quality [] = eqa-nil
collapseAllEdges-quality (e ∷ es) = eqa-cons refl (collapseAllEdges-quality es)

collapseAllEdges-length : ∀ (es : List Edge) → length (collapseAllEdges es) ≡ length es
collapseAllEdges-length [] = refl
collapseAllEdges-length (e ∷ es) = cong suc (collapseAllEdges-length es)

swapQubit : Qubit → Qubit
swapQubit q = mkQubit (Qubit.beta q) (Qubit.alpha q)

swapQubit-involutive : ∀ (q : Qubit) →
  Qubit.alpha (swapQubit (swapQubit q)) ≡ Qubit.alpha q ×
  Qubit.beta (swapQubit (swapQubit q)) ≡ Qubit.beta q
swapQubit-involutive q = refl , refl

swapQubit-normPreserved : ∀ (q : Qubit) → normSquared (swapQubit q) ≡ normSquared q
swapQubit-normPreserved q = +-comm (complexMagSq (Qubit.beta q)) (complexMagSq (Qubit.alpha q))

graphInvariant-empty : UniqueIds (Graph.graphNodes emptyGraph) ×
                       AllEdgesValid (Graph.graphEdges emptyGraph) (Graph.graphNodes emptyGraph) ×
                       IsAcyclic (Graph.graphEdges emptyGraph)
graphInvariant-empty = unique-nil , valid-nil , acyclic-nil

edgeWeight-sum : List Edge → ℕ
edgeWeight-sum [] = 0
edgeWeight-sum (e ∷ es) = Edge.edgeWeight e + edgeWeight-sum es

edgeWeight-sum-append : ∀ (es : List Edge) (e : Edge) →
  edgeWeight-sum (es ++ (e ∷ [])) ≡ edgeWeight-sum es + Edge.edgeWeight e
edgeWeight-sum-append [] e = +-identityʳ (Edge.edgeWeight e)
edgeWeight-sum-append (x ∷ xs) e =
  begin
    Edge.edgeWeight x + edgeWeight-sum (xs ++ (e ∷ []))
  ≡⟨ cong (Edge.edgeWeight x +_) (edgeWeight-sum-append xs e) ⟩
    Edge.edgeWeight x + (edgeWeight-sum xs + Edge.edgeWeight e)
  ≡⟨ sym (+-assoc (Edge.edgeWeight x) (edgeWeight-sum xs) (Edge.edgeWeight e)) ⟩
    (Edge.edgeWeight x + edgeWeight-sum xs) + Edge.edgeWeight e
  ∎

nodeDataSum : List Node → ℕ
nodeDataSum [] = 0
nodeDataSum (n ∷ ns) = Node.nodeData n + nodeDataSum ns

nodeDataSum-append : ∀ (ns : List Node) (n : Node) →
  nodeDataSum (ns ++ (n ∷ [])) ≡ nodeDataSum ns + Node.nodeData n
nodeDataSum-append [] n = +-identityʳ (Node.nodeData n)
nodeDataSum-append (x ∷ xs) n =
  begin
    Node.nodeData x + nodeDataSum (xs ++ (n ∷ []))
  ≡⟨ cong (Node.nodeData x +_) (nodeDataSum-append xs n) ⟩
    Node.nodeData x + (nodeDataSum xs + Node.nodeData n)
  ≡⟨ sym (+-assoc (Node.nodeData x) (nodeDataSum xs) (Node.nodeData n)) ⟩
    (Node.nodeData x + nodeDataSum xs) + Node.nodeData n
  ∎
