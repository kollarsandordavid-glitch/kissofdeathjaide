module Optimizer where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; _≥_; _>_; s≤s; z≤n; _⊔_; _⊓_; _≤?_; _<?_; _≡ᵇ_)
open import Data.Nat.Properties using (+-identityʳ; +-identityˡ; +-comm; +-assoc; +-suc; *-identityˡ; *-identityʳ; *-comm; *-assoc; *-distribˡ-+; *-distribʳ-+; ≤-refl; ≤-trans; ≤-antisym; ≤-step; m≤m+n; m+n∸n≡m; n∸n≡0; +-mono-≤; *-mono-≤; m≤n⇒m∸n≡0; suc-injective; m∸n+n≡m; n≤m+n; +-cancelˡ-≡; m+n∸m≡n)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_; T)
open import Data.Bool.Properties using (∧-comm; ∨-comm; ∧-assoc; ∨-assoc; not-involutive)
open import Data.List using (List; []; _∷_; length; map; filter; _++_; foldr; foldl; reverse; replicate; concat)
open import Data.List.Properties using (++-identityʳ; ++-assoc; length-++; length-replicate; length-map)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<)
open import Data.Vec using (Vec; []; _∷_; lookup; tabulate; toList) renaming (length to vlength; map to vmap; replicate to vreplicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no; does)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function using (_∘_; id; _$_; flip; const)

open ≡-Reasoning

data SymmetryGroup : Set where
  identity : SymmetryGroup
  reflection : SymmetryGroup
  rotation90 : SymmetryGroup
  rotation180 : SymmetryGroup
  rotation270 : SymmetryGroup
  translation : SymmetryGroup

_≟ₛ_ : (a b : SymmetryGroup) → Dec (a ≡ b)
identity ≟ₛ identity = yes refl
identity ≟ₛ reflection = no (λ ())
identity ≟ₛ rotation90 = no (λ ())
identity ≟ₛ rotation180 = no (λ ())
identity ≟ₛ rotation270 = no (λ ())
identity ≟ₛ translation = no (λ ())
reflection ≟ₛ identity = no (λ ())
reflection ≟ₛ reflection = yes refl
reflection ≟ₛ rotation90 = no (λ ())
reflection ≟ₛ rotation180 = no (λ ())
reflection ≟ₛ rotation270 = no (λ ())
reflection ≟ₛ translation = no (λ ())
rotation90 ≟ₛ identity = no (λ ())
rotation90 ≟ₛ reflection = no (λ ())
rotation90 ≟ₛ rotation90 = yes refl
rotation90 ≟ₛ rotation180 = no (λ ())
rotation90 ≟ₛ rotation270 = no (λ ())
rotation90 ≟ₛ translation = no (λ ())
rotation180 ≟ₛ identity = no (λ ())
rotation180 ≟ₛ reflection = no (λ ())
rotation180 ≟ₛ rotation90 = no (λ ())
rotation180 ≟ₛ rotation180 = yes refl
rotation180 ≟ₛ rotation270 = no (λ ())
rotation180 ≟ₛ translation = no (λ ())
rotation270 ≟ₛ identity = no (λ ())
rotation270 ≟ₛ reflection = no (λ ())
rotation270 ≟ₛ rotation90 = no (λ ())
rotation270 ≟ₛ rotation180 = no (λ ())
rotation270 ≟ₛ rotation270 = yes refl
rotation270 ≟ₛ translation = no (λ ())
translation ≟ₛ identity = no (λ ())
translation ≟ₛ reflection = no (λ ())
translation ≟ₛ rotation90 = no (λ ())
translation ≟ₛ rotation180 = no (λ ())
translation ≟ₛ rotation270 = no (λ ())
translation ≟ₛ translation = yes refl

getOrder : SymmetryGroup → ℕ
getOrder identity = 1
getOrder reflection = 2
getOrder rotation90 = 4
getOrder rotation180 = 2
getOrder rotation270 = 4
getOrder translation = 1

getOrder-pos : ∀ (g : SymmetryGroup) → getOrder g > 0
getOrder-pos identity = s≤s z≤n
getOrder-pos reflection = s≤s z≤n
getOrder-pos rotation90 = s≤s z≤n
getOrder-pos rotation180 = s≤s z≤n
getOrder-pos rotation270 = s≤s z≤n
getOrder-pos translation = s≤s z≤n

groupInverse : SymmetryGroup → SymmetryGroup
groupInverse identity = identity
groupInverse reflection = reflection
groupInverse rotation90 = rotation270
groupInverse rotation180 = rotation180
groupInverse rotation270 = rotation90
groupInverse translation = translation

groupCompose : SymmetryGroup → SymmetryGroup → SymmetryGroup
groupCompose identity g = g
groupCompose g identity = g
groupCompose rotation90 rotation90 = rotation180
groupCompose rotation90 rotation180 = rotation270
groupCompose rotation90 rotation270 = identity
groupCompose rotation180 rotation90 = rotation270
groupCompose rotation180 rotation180 = identity
groupCompose rotation180 rotation270 = rotation90
groupCompose rotation270 rotation90 = identity
groupCompose rotation270 rotation180 = rotation90
groupCompose rotation270 rotation270 = rotation180
groupCompose reflection reflection = identity
groupCompose reflection rotation90 = rotation90
groupCompose reflection rotation180 = rotation180
groupCompose reflection rotation270 = rotation270
groupCompose reflection translation = translation
groupCompose rotation90 reflection = rotation90
groupCompose rotation90 translation = rotation90
groupCompose rotation180 reflection = rotation180
groupCompose rotation180 translation = rotation180
groupCompose rotation270 reflection = rotation270
groupCompose rotation270 translation = rotation270
groupCompose translation reflection = translation
groupCompose translation rotation90 = translation
groupCompose translation rotation180 = translation
groupCompose translation rotation270 = translation
groupCompose translation translation = translation

compose-left-identity : ∀ (g : SymmetryGroup) → groupCompose identity g ≡ g
compose-left-identity identity = refl
compose-left-identity reflection = refl
compose-left-identity rotation90 = refl
compose-left-identity rotation180 = refl
compose-left-identity rotation270 = refl
compose-left-identity translation = refl

compose-right-identity : ∀ (g : SymmetryGroup) → groupCompose g identity ≡ g
compose-right-identity identity = refl
compose-right-identity reflection = refl
compose-right-identity rotation90 = refl
compose-right-identity rotation180 = refl
compose-right-identity rotation270 = refl
compose-right-identity translation = refl

compose-left-inverse : ∀ (g : SymmetryGroup) → groupCompose (groupInverse g) g ≡ identity
compose-left-inverse identity = refl
compose-left-inverse reflection = refl
compose-left-inverse rotation90 = refl
compose-left-inverse rotation180 = refl
compose-left-inverse rotation270 = refl
compose-left-inverse translation = refl

compose-right-inverse : ∀ (g : SymmetryGroup) → groupCompose g (groupInverse g) ≡ identity
compose-right-inverse identity = refl
compose-right-inverse reflection = refl
compose-right-inverse rotation90 = refl
compose-right-inverse rotation180 = refl
compose-right-inverse rotation270 = refl
compose-right-inverse translation = refl

inverse-involution : ∀ (g : SymmetryGroup) → groupInverse (groupInverse g) ≡ g
inverse-involution identity = refl
inverse-involution reflection = refl
inverse-involution rotation90 = refl
inverse-involution rotation180 = refl
inverse-involution rotation270 = refl
inverse-involution translation = refl

inverse-identity : groupInverse identity ≡ identity
inverse-identity = refl

inverse-reflection : groupInverse reflection ≡ reflection
inverse-reflection = refl

inverse-rotation180 : groupInverse rotation180 ≡ rotation180
inverse-rotation180 = refl

rotation90-compose-rotation90 : groupCompose rotation90 rotation90 ≡ rotation180
rotation90-compose-rotation90 = refl

rotation90-compose-rotation180 : groupCompose rotation90 rotation180 ≡ rotation270
rotation90-compose-rotation180 = refl

rotation180-compose-rotation180 : groupCompose rotation180 rotation180 ≡ identity
rotation180-compose-rotation180 = refl

rotation270-compose-rotation90 : groupCompose rotation270 rotation90 ≡ identity
rotation270-compose-rotation90 = refl

rotation90-four-fold : groupCompose rotation90 (groupCompose rotation90 (groupCompose rotation90 rotation90)) ≡ identity
rotation90-four-fold = refl

reflection-self-inverse : groupCompose reflection reflection ≡ identity
reflection-self-inverse = refl

rotation-cycle-90-180 : groupCompose rotation90 rotation90 ≡ rotation180
rotation-cycle-90-180 = refl

rotation-cycle-90-270 : groupCompose rotation90 rotation180 ≡ rotation270
rotation-cycle-90-270 = refl

rotation-cycle-270-identity : groupCompose rotation270 rotation90 ≡ identity
rotation-cycle-270-identity = refl

inverse-compose-dist : ∀ (g : SymmetryGroup) → groupCompose (groupInverse g) g ≡ groupCompose g (groupInverse g)
inverse-compose-dist identity = refl
inverse-compose-dist reflection = refl
inverse-compose-dist rotation90 = refl
inverse-compose-dist rotation180 = refl
inverse-compose-dist rotation270 = refl
inverse-compose-dist translation = refl

record Point : Set where
  field
    px : ℕ
    py : ℕ

mkPoint : ℕ → ℕ → Point
mkPoint x y = record { px = x ; py = y }

point-eq : ∀ (p : Point) → mkPoint (Point.px p) (Point.py p) ≡ p
point-eq record { px = x ; py = y } = refl

applyIdentity : Point → Point
applyIdentity p = p

applyRotation180 : Point → ℕ → ℕ → Point
applyRotation180 p ox oy = record
  { px = ox + (ox ∸ Point.px p)
  ; py = oy + (oy ∸ Point.py p)
  }

applyTranslation : Point → ℕ → ℕ → Point
applyTranslation p dx dy = record
  { px = Point.px p + dx
  ; py = Point.py p + dy
  }

identity-preserves-point : ∀ (p : Point) → applyIdentity p ≡ p
identity-preserves-point p = refl

translation-zero-identity : ∀ (p : Point) → applyTranslation p 0 0 ≡ record { px = Point.px p ; py = Point.py p }
translation-zero-identity p = cong₂ (λ a b → record { px = a ; py = b }) (+-identityʳ (Point.px p)) (+-identityʳ (Point.py p))

record SymmetryTransform : Set where
  field
    group : SymmetryGroup
    originX : ℕ
    originY : ℕ
    param0 : ℕ
    param1 : ℕ
    param2 : ℕ
    param3 : ℕ
    scaleFactor : ℕ

mkTransform : SymmetryGroup → SymmetryTransform
mkTransform g = record
  { group = g
  ; originX = 0
  ; originY = 0
  ; param0 = 0
  ; param1 = 0
  ; param2 = 1
  ; param3 = 0
  ; scaleFactor = 1
  }

mkTransformWithParams : SymmetryGroup → ℕ → ℕ → ℕ → ℕ → SymmetryTransform
mkTransformWithParams g p0 p1 p2 p3 = record
  { group = g
  ; originX = p0
  ; originY = p1
  ; param0 = p0
  ; param1 = p1
  ; param2 = if p2 ≡ᵇ 0 then 1 else p2
  ; param3 = p3
  ; scaleFactor = if p2 ≡ᵇ 0 then 1 else p2
  }

transformInverse : SymmetryTransform → SymmetryTransform
transformInverse t = record
  { group = groupInverse (SymmetryTransform.group t)
  ; originX = SymmetryTransform.originX t
  ; originY = SymmetryTransform.originY t
  ; param0 = SymmetryTransform.param0 t
  ; param1 = SymmetryTransform.param1 t
  ; param2 = SymmetryTransform.param2 t
  ; param3 = SymmetryTransform.param3 t
  ; scaleFactor = SymmetryTransform.scaleFactor t
  }

transformCompose : SymmetryTransform → SymmetryTransform → SymmetryTransform
transformCompose t1 t2 = record
  { group = groupCompose (SymmetryTransform.group t1) (SymmetryTransform.group t2)
  ; originX = SymmetryTransform.originX t1
  ; originY = SymmetryTransform.originY t1
  ; param0 = SymmetryTransform.param0 t1 + SymmetryTransform.param0 t2
  ; param1 = SymmetryTransform.param1 t1 + SymmetryTransform.param1 t2
  ; param2 = SymmetryTransform.param2 t1
  ; param3 = SymmetryTransform.param3 t1
  ; scaleFactor = SymmetryTransform.scaleFactor t1
  }

inverse-group-correct : ∀ (t : SymmetryTransform) →
  SymmetryTransform.group (transformInverse t) ≡ groupInverse (SymmetryTransform.group t)
inverse-group-correct t = refl

inverse-preserves-origin-x : ∀ (t : SymmetryTransform) →
  SymmetryTransform.originX (transformInverse t) ≡ SymmetryTransform.originX t
inverse-preserves-origin-x t = refl

inverse-preserves-origin-y : ∀ (t : SymmetryTransform) →
  SymmetryTransform.originY (transformInverse t) ≡ SymmetryTransform.originY t
inverse-preserves-origin-y t = refl

inverse-preserves-scale : ∀ (t : SymmetryTransform) →
  SymmetryTransform.scaleFactor (transformInverse t) ≡ SymmetryTransform.scaleFactor t
inverse-preserves-scale t = refl

compose-group-correct : ∀ (t1 t2 : SymmetryTransform) →
  SymmetryTransform.group (transformCompose t1 t2) ≡ groupCompose (SymmetryTransform.group t1) (SymmetryTransform.group t2)
compose-group-correct t1 t2 = refl

identity-transform-group : SymmetryTransform.group (mkTransform identity) ≡ identity
identity-transform-group = refl

compose-identity-left : ∀ (t : SymmetryTransform) →
  SymmetryTransform.group (transformCompose (mkTransform identity) t) ≡ SymmetryTransform.group t
compose-identity-left t = compose-left-identity (SymmetryTransform.group t)

compose-identity-right : ∀ (t : SymmetryTransform) →
  SymmetryTransform.group (transformCompose t (mkTransform identity)) ≡ SymmetryTransform.group t
compose-identity-right t = compose-right-identity (SymmetryTransform.group t)

inverse-then-compose-identity : ∀ (t : SymmetryTransform) →
  SymmetryTransform.group (transformCompose (transformInverse t) t) ≡ identity
inverse-then-compose-identity t =
  begin
    SymmetryTransform.group (transformCompose (transformInverse t) t)
  ≡⟨ compose-group-correct (transformInverse t) t ⟩
    groupCompose (groupInverse (SymmetryTransform.group t)) (SymmetryTransform.group t)
  ≡⟨ compose-left-inverse (SymmetryTransform.group t) ⟩
    identity
  ∎

compose-then-inverse-identity : ∀ (t : SymmetryTransform) →
  SymmetryTransform.group (transformCompose t (transformInverse t)) ≡ identity
compose-then-inverse-identity t =
  begin
    SymmetryTransform.group (transformCompose t (transformInverse t))
  ≡⟨ compose-group-correct t (transformInverse t) ⟩
    groupCompose (SymmetryTransform.group t) (groupInverse (SymmetryTransform.group t))
  ≡⟨ compose-right-inverse (SymmetryTransform.group t) ⟩
    identity
  ∎

double-inverse-identity : ∀ (t : SymmetryTransform) →
  SymmetryTransform.group (transformInverse (transformInverse t)) ≡ SymmetryTransform.group t
double-inverse-identity t =
  begin
    SymmetryTransform.group (transformInverse (transformInverse t))
  ≡⟨ inverse-group-correct (transformInverse t) ⟩
    groupInverse (SymmetryTransform.group (transformInverse t))
  ≡⟨ cong groupInverse (inverse-group-correct t) ⟩
    groupInverse (groupInverse (SymmetryTransform.group t))
  ≡⟨ inverse-involution (SymmetryTransform.group t) ⟩
    SymmetryTransform.group t
  ∎

record GraphState : Set where
  field
    nodeCount : ℕ
    edgeCount : ℕ
    totalWeight : ℕ
    coherence : ℕ
    edgeBound : edgeCount ≤ nodeCount * nodeCount

emptyGraph : GraphState
emptyGraph = record
  { nodeCount = 0
  ; edgeCount = 0
  ; totalWeight = 0
  ; coherence = 0
  ; edgeBound = z≤n
  }

emptyGraph-nodeCount : GraphState.nodeCount emptyGraph ≡ 0
emptyGraph-nodeCount = refl

emptyGraph-edgeCount : GraphState.edgeCount emptyGraph ≡ 0
emptyGraph-edgeCount = refl

record ClonedGraph : Set where
  field
    original : GraphState
    clone : GraphState
    nodeCountEq : GraphState.nodeCount original ≡ GraphState.nodeCount clone
    edgeCountEq : GraphState.edgeCount original ≡ GraphState.edgeCount clone
    weightEq : GraphState.totalWeight original ≡ GraphState.totalWeight clone
    coherenceEq : GraphState.coherence original ≡ GraphState.coherence clone

cloneGraph : (g : GraphState) → ClonedGraph
cloneGraph g = record
  { original = g
  ; clone = g
  ; nodeCountEq = refl
  ; edgeCountEq = refl
  ; weightEq = refl
  ; coherenceEq = refl
  }

clone-preserves-nodes : ∀ (g : GraphState) →
  GraphState.nodeCount (ClonedGraph.original (cloneGraph g)) ≡ GraphState.nodeCount (ClonedGraph.clone (cloneGraph g))
clone-preserves-nodes g = refl

clone-preserves-edges : ∀ (g : GraphState) →
  GraphState.edgeCount (ClonedGraph.original (cloneGraph g)) ≡ GraphState.edgeCount (ClonedGraph.clone (cloneGraph g))
clone-preserves-edges g = refl

clone-preserves-weight : ∀ (g : GraphState) →
  GraphState.totalWeight (ClonedGraph.original (cloneGraph g)) ≡ GraphState.totalWeight (ClonedGraph.clone (cloneGraph g))
clone-preserves-weight g = refl

clone-preserves-coherence : ∀ (g : GraphState) →
  GraphState.coherence (ClonedGraph.original (cloneGraph g)) ≡ GraphState.coherence (ClonedGraph.clone (cloneGraph g))
clone-preserves-coherence g = refl

clone-symmetric : ∀ (g : GraphState) →
  GraphState.nodeCount (ClonedGraph.clone (cloneGraph g)) ≡ GraphState.nodeCount (ClonedGraph.original (cloneGraph g))
clone-symmetric g = sym (clone-preserves-nodes g)

record ObjectiveValue : Set where
  field
    energy : ℕ

objectiveFunction : GraphState → ObjectiveValue
objectiveFunction g = record
  { energy = GraphState.totalWeight g + GraphState.coherence g
  }

clone-preserves-objective : ∀ (g : GraphState) →
  objectiveFunction (ClonedGraph.original (cloneGraph g)) ≡ objectiveFunction (ClonedGraph.clone (cloneGraph g))
clone-preserves-objective g = refl

record OptimizationConfig : Set where
  field
    maxIterations : ℕ
    initialTemp : ℕ
    coolingRate : ℕ
    minTemp : ℕ
    tempBound : minTemp ≤ initialTemp

defaultOptConfig : OptimizationConfig
defaultOptConfig = record
  { maxIterations = 10000
  ; initialTemp = 100
  ; coolingRate = 95
  ; minTemp = 1
  ; tempBound = s≤s z≤n
  }

record OptimizationStep : Set where
  field
    iteration : ℕ
    temperature : ℕ
    currentEnergy : ℕ
    bestEnergy : ℕ
    bestBound : bestEnergy ≤ currentEnergy

initialStep : ℕ → OptimizationStep
initialStep e = record
  { iteration = 0
  ; temperature = 100
  ; currentEnergy = e
  ; bestEnergy = e
  ; bestBound = ≤-refl
  }

initialStep-iteration : ∀ (e : ℕ) → OptimizationStep.iteration (initialStep e) ≡ 0
initialStep-iteration e = refl

initialStep-best-eq-current : ∀ (e : ℕ) →
  OptimizationStep.bestEnergy (initialStep e) ≡ OptimizationStep.currentEnergy (initialStep e)
initialStep-best-eq-current e = refl

data MoveResult : Set where
  accepted : ℕ → MoveResult
  rejected : MoveResult

applyMove : OptimizationStep → ℕ → OptimizationStep
applyMove step newEnergy with newEnergy ≤? OptimizationStep.currentEnergy step
... | yes p = record
  { iteration = suc (OptimizationStep.iteration step)
  ; temperature = OptimizationStep.temperature step
  ; currentEnergy = newEnergy
  ; bestEnergy = newEnergy ⊓ OptimizationStep.bestEnergy step
  ; bestBound = helper newEnergy (OptimizationStep.bestEnergy step) p (OptimizationStep.bestBound step)
  }
  where
    helper : ∀ (a b : ℕ) → a ≤ OptimizationStep.currentEnergy step → b ≤ OptimizationStep.currentEnergy step → a ⊓ b ≤ a
    helper zero b _ _ = z≤n
    helper (suc a) zero _ _ = z≤n
    helper (suc a) (suc b) p1 p2 with a ≤? b
    ... | yes _ = ≤-refl
    ... | no _ = m≤m+n (suc b) (a ∸ b)
... | no _ = record
  { iteration = suc (OptimizationStep.iteration step)
  ; temperature = OptimizationStep.temperature step
  ; currentEnergy = OptimizationStep.currentEnergy step
  ; bestEnergy = OptimizationStep.bestEnergy step
  ; bestBound = OptimizationStep.bestBound step
  }

applyMove-increments-iteration : ∀ (step : OptimizationStep) (e : ℕ) →
  OptimizationStep.iteration (applyMove step e) ≡ suc (OptimizationStep.iteration step)
applyMove-increments-iteration step e with e ≤? OptimizationStep.currentEnergy step
... | yes _ = refl
... | no _ = refl

coolTemperature : ℕ → ℕ → ℕ
coolTemperature temp rate = (temp * rate) / 100
  where
    _/_ : ℕ → ℕ → ℕ
    _ / 0 = 0
    a / (suc b) = go a (suc b) a
      where
        go : ℕ → ℕ → ℕ → ℕ
        go _ _ 0 = 0
        go 0 _ _ = 0
        go a b (suc fuel) with a <? b
        ... | yes _ = 0
        ... | no _ = suc (go (a ∸ b) b fuel)

coolTemperature-zero : ∀ (rate : ℕ) → coolTemperature 0 rate ≡ 0
coolTemperature-zero rate = refl

record OptimizationStatistics : Set where
  field
    iterationsCompleted : ℕ
    movesAccepted : ℕ
    movesRejected : ℕ
    bestEnergy : ℕ
    symmetriesDetected : ℕ
    entangledPairs : ℕ
    totalMoves : ℕ
    movesConsistency : movesAccepted + movesRejected ≡ totalMoves

emptyStatistics : OptimizationStatistics
emptyStatistics = record
  { iterationsCompleted = 0
  ; movesAccepted = 0
  ; movesRejected = 0
  ; bestEnergy = 0
  ; symmetriesDetected = 0
  ; entangledPairs = 0
  ; totalMoves = 0
  ; movesConsistency = refl
  }

emptyStats-zero-iterations : OptimizationStatistics.iterationsCompleted emptyStatistics ≡ 0
emptyStats-zero-iterations = refl

emptyStats-zero-accepted : OptimizationStatistics.movesAccepted emptyStatistics ≡ 0
emptyStats-zero-accepted = refl

emptyStats-zero-rejected : OptimizationStatistics.movesRejected emptyStatistics ≡ 0
emptyStats-zero-rejected = refl

record EntanglementInfo : Set where
  field
    correlationStrength : ℕ
    phaseDifference : ℕ
    interactionCount : ℕ

emptyEntanglement : EntanglementInfo
emptyEntanglement = record
  { correlationStrength = 0
  ; phaseDifference = 0
  ; interactionCount = 0
  }

updateEntanglement : EntanglementInfo → ℕ → ℕ → EntanglementInfo
updateEntanglement info newCorr newPhase = record
  { correlationStrength = (EntanglementInfo.correlationStrength info + newCorr) / 2
  ; phaseDifference = (EntanglementInfo.phaseDifference info + newPhase) / 2
  ; interactionCount = suc (EntanglementInfo.interactionCount info)
  }
  where
    _/_ : ℕ → ℕ → ℕ
    _ / 0 = 0
    a / (suc b) = go a (suc b) a
      where
        go : ℕ → ℕ → ℕ → ℕ
        go _ _ 0 = 0
        go 0 _ _ = 0
        go a b (suc fuel) with a <? b
        ... | yes _ = 0
        ... | no _ = suc (go (a ∸ b) b fuel)

update-increments-interaction : ∀ (info : EntanglementInfo) (c p : ℕ) →
  EntanglementInfo.interactionCount (updateEntanglement info c p) ≡ suc (EntanglementInfo.interactionCount info)
update-increments-interaction info c p = refl

record SymmetryPattern : Set where
  field
    transform : SymmetryTransform
    nodeIds : List ℕ
    symmetryScore : ℕ
    resonanceFreq : ℕ

emptyPattern : SymmetryTransform → SymmetryPattern
emptyPattern t = record
  { transform = t
  ; nodeIds = []
  ; symmetryScore = 0
  ; resonanceFreq = 0
  }

addNodeToPattern : SymmetryPattern → ℕ → SymmetryPattern
addNodeToPattern pat nid = record pat { nodeIds = SymmetryPattern.nodeIds pat ++ (nid ∷ []) }

addNode-increases-length : ∀ (pat : SymmetryPattern) (nid : ℕ) →
  length (SymmetryPattern.nodeIds (addNodeToPattern pat nid)) ≡ suc (length (SymmetryPattern.nodeIds pat))
addNode-increases-length pat nid =
  begin
    length (SymmetryPattern.nodeIds pat ++ (nid ∷ []))
  ≡⟨ length-++ (SymmetryPattern.nodeIds pat) ⟩
    length (SymmetryPattern.nodeIds pat) + length (nid ∷ [])
  ≡⟨ cong (length (SymmetryPattern.nodeIds pat) +_) refl ⟩
    length (SymmetryPattern.nodeIds pat) + 1
  ≡⟨ +-comm (length (SymmetryPattern.nodeIds pat)) 1 ⟩
    suc (length (SymmetryPattern.nodeIds pat))
  ∎

emptyPattern-no-nodes : ∀ (t : SymmetryTransform) → length (SymmetryPattern.nodeIds (emptyPattern t)) ≡ 0
emptyPattern-no-nodes t = refl

record ConvergenceBound : Set where
  field
    initialEnergy : ℕ
    finalEnergy : ℕ
    steps : ℕ
    monotone : finalEnergy ≤ initialEnergy

trivialConvergence : ∀ (e : ℕ) → ConvergenceBound
trivialConvergence e = record
  { initialEnergy = e
  ; finalEnergy = e
  ; steps = 0
  ; monotone = ≤-refl
  }

trivialConvergence-zero-steps : ∀ (e : ℕ) → ConvergenceBound.steps (trivialConvergence e) ≡ 0
trivialConvergence-zero-steps e = refl

trivialConvergence-energy-eq : ∀ (e : ℕ) →
  ConvergenceBound.initialEnergy (trivialConvergence e) ≡ ConvergenceBound.finalEnergy (trivialConvergence e)
trivialConvergence-energy-eq e = refl

stepConvergence : ∀ (init final : ℕ) → final ≤ init → ConvergenceBound
stepConvergence init final p = record
  { initialEnergy = init
  ; finalEnergy = final
  ; steps = 1
  ; monotone = p
  }

chainConvergence : ConvergenceBound → ConvergenceBound →
  ConvergenceBound.finalEnergy (record { initialEnergy = _; finalEnergy = _; steps = _; monotone = _ }) ≡
  ConvergenceBound.initialEnergy (record { initialEnergy = _; finalEnergy = _; steps = _; monotone = _ }) →
  ConvergenceBound
chainConvergence b1 b2 _ = record
  { initialEnergy = ConvergenceBound.initialEnergy b1
  ; finalEnergy = ConvergenceBound.finalEnergy b2
  ; steps = ConvergenceBound.steps b1 + ConvergenceBound.steps b2
  ; monotone = ≤-trans (ConvergenceBound.monotone b2) (≤-trans (ConvergenceBound.monotone b1) ≤-refl)
  }

convergence-transitive : ∀ (a b c : ℕ) → c ≤ b → b ≤ a → c ≤ a
convergence-transitive a b c c≤b b≤a = ≤-trans c≤b b≤a

energy-monotone-step : ∀ (e₁ e₂ : ℕ) → e₂ ≤ e₁ → e₂ ≤ e₁
energy-monotone-step e₁ e₂ p = p

energy-monotone-chain : ∀ (e₁ e₂ e₃ : ℕ) → e₂ ≤ e₁ → e₃ ≤ e₂ → e₃ ≤ e₁
energy-monotone-chain e₁ e₂ e₃ p q = ≤-trans q p

objectiveMonotone : ∀ (g : GraphState) (w₁ w₂ : ℕ) →
  w₂ ≤ w₁ →
  w₂ + GraphState.coherence g ≤ w₁ + GraphState.coherence g
objectiveMonotone g w₁ w₂ p = +-mono-≤ p ≤-refl

record OptimizerState : Set where
  field
    temperature : ℕ
    currentIteration : ℕ
    maxIterations : ℕ
    currentEnergy : ℕ
    bestEnergy : ℕ
    bestBound : bestEnergy ≤ currentEnergy
    iterationBound : currentIteration ≤ maxIterations

initialOptimizer : ℕ → ℕ → ℕ → OptimizerState
initialOptimizer temp maxIter energy = record
  { temperature = temp
  ; currentIteration = 0
  ; maxIterations = maxIter
  ; currentEnergy = energy
  ; bestEnergy = energy
  ; bestBound = ≤-refl
  ; iterationBound = z≤n
  }

initialOptimizer-at-start : ∀ (t m e : ℕ) →
  OptimizerState.currentIteration (initialOptimizer t m e) ≡ 0
initialOptimizer-at-start t m e = refl

initialOptimizer-best-eq : ∀ (t m e : ℕ) →
  OptimizerState.bestEnergy (initialOptimizer t m e) ≡ OptimizerState.currentEnergy (initialOptimizer t m e)
initialOptimizer-best-eq t m e = refl

data IsConverged : OptimizerState → Set where
  converged-by-temp : ∀ {s} → OptimizerState.temperature s ≡ 0 → IsConverged s
  converged-by-iter : ∀ {s} → OptimizerState.currentIteration s ≡ OptimizerState.maxIterations s → IsConverged s

zeroTemp-converged : ∀ (s : OptimizerState) → OptimizerState.temperature s ≡ 0 → IsConverged s
zeroTemp-converged s p = converged-by-temp p

maxIter-converged : ∀ (s : OptimizerState) → OptimizerState.currentIteration s ≡ OptimizerState.maxIterations s → IsConverged s
maxIter-converged s p = converged-by-iter p

data DetectedSymmetry : Set where
  noSymmetry : DetectedSymmetry
  foundSymmetry : SymmetryGroup → DetectedSymmetry

detectSymmetry : GraphState → DetectedSymmetry
detectSymmetry g with GraphState.nodeCount g
... | 0 = foundSymmetry identity
... | suc n with GraphState.edgeCount g ≤? (suc n * suc n)
...   | yes _ = foundSymmetry rotation90
...   | no _ = foundSymmetry identity

detect-always-finds : ∀ (g : GraphState) → ∃[ r ] (detectSymmetry g ≡ r)
detect-always-finds g = detectSymmetry g , refl

identity-always-detected : detectSymmetry emptyGraph ≡ foundSymmetry identity
identity-always-detected = refl

record AcceptanceDecision : Set where
  field
    accepted : Bool
    energyDelta : ℕ

shouldAccept : ℕ → ℕ → ℕ → Bool
shouldAccept newE oldE temp = newE ≤ᵇ oldE ∨ (0 <ᵇ temp)
  where
    _≤ᵇ_ : ℕ → ℕ → Bool
    zero ≤ᵇ _ = true
    suc _ ≤ᵇ zero = false
    suc a ≤ᵇ suc b = a ≤ᵇ b

    _<ᵇ_ : ℕ → ℕ → Bool
    _ <ᵇ zero = false
    zero <ᵇ suc _ = true
    suc a <ᵇ suc b = a <ᵇ b

better-energy-accepted : ∀ (temp : ℕ) → shouldAccept 0 1 temp ≡ true
better-energy-accepted temp = refl

rotationSubgroup : List SymmetryGroup
rotationSubgroup = identity ∷ rotation90 ∷ rotation180 ∷ rotation270 ∷ []

rotationSubgroup-length : length rotationSubgroup ≡ 4
rotationSubgroup-length = refl

rotationClosed : ∀ (a b : SymmetryGroup) →
  (a ≡ identity ⊎ a ≡ rotation90 ⊎ a ≡ rotation180 ⊎ a ≡ rotation270) →
  (b ≡ identity ⊎ b ≡ rotation90 ⊎ b ≡ rotation180 ⊎ b ≡ rotation270) →
  (groupCompose a b ≡ identity ⊎ groupCompose a b ≡ rotation90 ⊎ groupCompose a b ≡ rotation180 ⊎ groupCompose a b ≡ rotation270)
rotationClosed .identity b (inj₁ refl) qb =
  subst (λ x → x ≡ identity ⊎ x ≡ rotation90 ⊎ x ≡ rotation180 ⊎ x ≡ rotation270) (sym (compose-left-identity b)) qb
rotationClosed .rotation90 .identity (inj₂ (inj₁ refl)) (inj₁ refl) = inj₂ (inj₁ refl)
rotationClosed .rotation90 .rotation90 (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) = inj₂ (inj₂ (inj₁ refl))
rotationClosed .rotation90 .rotation180 (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₁ refl))) = inj₂ (inj₂ (inj₂ refl))
rotationClosed .rotation90 .rotation270 (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ refl))) = inj₁ refl
rotationClosed .rotation180 .identity (inj₂ (inj₂ (inj₁ refl))) (inj₁ refl) = inj₂ (inj₂ (inj₁ refl))
rotationClosed .rotation180 .rotation90 (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₁ refl)) = inj₂ (inj₂ (inj₂ refl))
rotationClosed .rotation180 .rotation180 (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₁ refl))) = inj₁ refl
rotationClosed .rotation180 .rotation270 (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ refl))) = inj₂ (inj₁ refl)
rotationClosed .rotation270 .identity (inj₂ (inj₂ (inj₂ refl))) (inj₁ refl) = inj₂ (inj₂ (inj₂ refl))
rotationClosed .rotation270 .rotation90 (inj₂ (inj₂ (inj₂ refl))) (inj₂ (inj₁ refl)) = inj₁ refl
rotationClosed .rotation270 .rotation180 (inj₂ (inj₂ (inj₂ refl))) (inj₂ (inj₂ (inj₁ refl))) = inj₂ (inj₁ refl)
rotationClosed .rotation270 .rotation270 (inj₂ (inj₂ (inj₂ refl))) (inj₂ (inj₂ (inj₂ refl))) = inj₂ (inj₂ (inj₁ refl))

rotationInverseClosed : ∀ (a : SymmetryGroup) →
  (a ≡ identity ⊎ a ≡ rotation90 ⊎ a ≡ rotation180 ⊎ a ≡ rotation270) →
  (groupInverse a ≡ identity ⊎ groupInverse a ≡ rotation90 ⊎ groupInverse a ≡ rotation180 ⊎ groupInverse a ≡ rotation270)
rotationInverseClosed .identity (inj₁ refl) = inj₁ refl
rotationInverseClosed .rotation90 (inj₂ (inj₁ refl)) = inj₂ (inj₂ (inj₂ refl))
rotationInverseClosed .rotation180 (inj₂ (inj₂ (inj₁ refl))) = inj₂ (inj₂ (inj₁ refl))
rotationInverseClosed .rotation270 (inj₂ (inj₂ (inj₂ refl))) = inj₂ (inj₁ refl)

identityInRotation : identity ≡ identity ⊎ identity ≡ rotation90 ⊎ identity ≡ rotation180 ⊎ identity ≡ rotation270
identityInRotation = inj₁ refl

optimizationBound : ∀ (best current : ℕ) → best ≤ current → best ≤ current + 0
optimizationBound best current p = subst (best ≤_) (sym (+-identityʳ current)) p

optimizationBound' : ∀ (best current extra : ℕ) → best ≤ current → best ≤ current + extra
optimizationBound' best current extra p = ≤-trans p (m≤m+n current extra)

iterationProgress : ∀ (i max : ℕ) → i < max → suc i ≤ max
iterationProgress i max p = p

convergenceBoundExists : ∀ (e : ℕ) → ∃[ b ] (ConvergenceBound.finalEnergy b ≤ e)
convergenceBoundExists e = trivialConvergence e , ≤-refl

multiStepConvergence : ∀ (e₁ e₂ e₃ : ℕ) → e₂ ≤ e₁ → e₃ ≤ e₂ →
  ∃[ b ] (ConvergenceBound.initialEnergy b ≡ e₁ × ConvergenceBound.finalEnergy b ≡ e₃)
multiStepConvergence e₁ e₂ e₃ p q =
  record { initialEnergy = e₁ ; finalEnergy = e₃ ; steps = 2 ; monotone = ≤-trans q p } , refl , refl

translationComposeParams : ∀ (a b c d : ℕ) →
  a + c + (b + d) ≡ b + d + (a + c)
translationComposeParams a b c d = +-comm (a + c) (b + d)

symmetryOrderBound : ∀ (g : SymmetryGroup) → getOrder g ≤ 4
symmetryOrderBound identity = s≤s z≤n
symmetryOrderBound reflection = s≤s (s≤s z≤n)
symmetryOrderBound rotation90 = ≤-refl
symmetryOrderBound rotation180 = s≤s (s≤s z≤n)
symmetryOrderBound rotation270 = ≤-refl
symmetryOrderBound translation = s≤s z≤n

symmetryOrderPos : ∀ (g : SymmetryGroup) → 0 < getOrder g
symmetryOrderPos = getOrder-pos

allGroupElements : List SymmetryGroup
allGroupElements = identity ∷ reflection ∷ rotation90 ∷ rotation180 ∷ rotation270 ∷ translation ∷ []

allGroupElements-length : length allGroupElements ≡ 6
allGroupElements-length = refl

compose-assoc-rotations : groupCompose (groupCompose rotation90 rotation90) rotation90 ≡
                          groupCompose rotation90 (groupCompose rotation90 rotation90)
compose-assoc-rotations = refl

compose-assoc-mixed : groupCompose (groupCompose rotation90 rotation180) rotation270 ≡
                      groupCompose rotation90 (groupCompose rotation180 rotation270)
compose-assoc-mixed = refl

compose-assoc-identity : ∀ (a b : SymmetryGroup) →
  groupCompose (groupCompose identity a) b ≡ groupCompose identity (groupCompose a b)
compose-assoc-identity a b =
  begin
    groupCompose (groupCompose identity a) b
  ≡⟨ cong (λ x → groupCompose x b) (compose-left-identity a) ⟩
    groupCompose a b
  ≡⟨ sym (compose-left-identity (groupCompose a b)) ⟩
    groupCompose identity (groupCompose a b)
  ∎

record TransformEquivalence (t1 t2 : SymmetryTransform) : Set where
  field
    groupEq : SymmetryTransform.group t1 ≡ SymmetryTransform.group t2
    originXEq : SymmetryTransform.originX t1 ≡ SymmetryTransform.originX t2
    originYEq : SymmetryTransform.originY t1 ≡ SymmetryTransform.originY t2

transformEquiv-refl : ∀ (t : SymmetryTransform) → TransformEquivalence t t
transformEquiv-refl t = record
  { groupEq = refl
  ; originXEq = refl
  ; originYEq = refl
  }

transformEquiv-sym : ∀ {t1 t2 : SymmetryTransform} → TransformEquivalence t1 t2 → TransformEquivalence t2 t1
transformEquiv-sym eq = record
  { groupEq = sym (TransformEquivalence.groupEq eq)
  ; originXEq = sym (TransformEquivalence.originXEq eq)
  ; originYEq = sym (TransformEquivalence.originYEq eq)
  }

transformEquiv-trans : ∀ {t1 t2 t3 : SymmetryTransform} → TransformEquivalence t1 t2 → TransformEquivalence t2 t3 → TransformEquivalence t1 t3
transformEquiv-trans eq1 eq2 = record
  { groupEq = trans (TransformEquivalence.groupEq eq1) (TransformEquivalence.groupEq eq2)
  ; originXEq = trans (TransformEquivalence.originXEq eq1) (TransformEquivalence.originXEq eq2)
  ; originYEq = trans (TransformEquivalence.originYEq eq1) (TransformEquivalence.originYEq eq2)
  }

inverse-inverse-equiv : ∀ (t : SymmetryTransform) →
  TransformEquivalence (transformInverse (transformInverse t)) t
inverse-inverse-equiv t = record
  { groupEq = double-inverse-identity t
  ; originXEq = refl
  ; originYEq = refl
  }

mkTransform-identity-is-identity : SymmetryTransform.group (mkTransform identity) ≡ identity
mkTransform-identity-is-identity = refl

mkTransform-rotation90-correct : SymmetryTransform.group (mkTransform rotation90) ≡ rotation90
mkTransform-rotation90-correct = refl

inverse-rotation90-is-rotation270 : SymmetryTransform.group (transformInverse (mkTransform rotation90)) ≡ rotation270
inverse-rotation90-is-rotation270 = refl

inverse-rotation270-is-rotation90 : SymmetryTransform.group (transformInverse (mkTransform rotation270)) ≡ rotation90
inverse-rotation270-is-rotation90 = refl

compose-rot90-rot90-is-rot180 : SymmetryTransform.group (transformCompose (mkTransform rotation90) (mkTransform rotation90)) ≡ rotation180
compose-rot90-rot90-is-rot180 = refl

compose-rot90-rot180-is-rot270 : SymmetryTransform.group (transformCompose (mkTransform rotation90) (mkTransform rotation180)) ≡ rotation270
compose-rot90-rot180-is-rot270 = refl

compose-rot180-rot180-is-identity : SymmetryTransform.group (transformCompose (mkTransform rotation180) (mkTransform rotation180)) ≡ identity
compose-rot180-rot180-is-identity = refl

compose-rot270-rot90-is-identity : SymmetryTransform.group (transformCompose (mkTransform rotation270) (mkTransform rotation90)) ≡ identity
compose-rot270-rot90-is-identity = refl

energyBound-preserved : ∀ (best cur new : ℕ) → best ≤ cur → new ≤ cur → best ⊓ new ≤ cur
energyBound-preserved zero cur new _ _ = z≤n
energyBound-preserved (suc b) zero new () _
energyBound-preserved (suc b) (suc c) zero _ _ = z≤n
energyBound-preserved (suc b) (suc c) (suc n) (s≤s p) (s≤s q) with b ≤? n
... | yes _ = s≤s p
... | no _ = s≤s q

optimization-never-worse : ∀ (step : OptimizationStep) →
  OptimizationStep.bestEnergy step ≤ OptimizationStep.currentEnergy step
optimization-never-worse step = OptimizationStep.bestBound step

optimizer-initial-sound : ∀ (t m e : ℕ) →
  OptimizerState.bestEnergy (initialOptimizer t m e) ≤ OptimizerState.currentEnergy (initialOptimizer t m e)
optimizer-initial-sound t m e = ≤-refl

optimizer-initial-iteration-bound : ∀ (t m e : ℕ) →
  OptimizerState.currentIteration (initialOptimizer t m e) ≤ OptimizerState.maxIterations (initialOptimizer t m e)
optimizer-initial-iteration-bound t m e = z≤n
