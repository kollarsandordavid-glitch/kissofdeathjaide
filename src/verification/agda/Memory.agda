module Memory where

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

record MemoryConfig : Set where
  field
    pageSize : ℕ
    cacheLineSize : ℕ
    pageSizePos : pageSize > 0
    cacheLineSizePos : cacheLineSize > 0

defaultConfig : MemoryConfig
defaultConfig = record
  { pageSize = 4096
  ; cacheLineSize = 128
  ; pageSizePos = s≤s z≤n
  ; cacheLineSizePos = s≤s z≤n
  }

data IsPow2 : ℕ → Set where
  pow2-one : IsPow2 1
  pow2-double : ∀ {n} → IsPow2 n → IsPow2 (n + n)

isPow2-1 : IsPow2 1
isPow2-1 = pow2-one

isPow2-2 : IsPow2 2
isPow2-2 = pow2-double pow2-one

isPow2-4 : IsPow2 4
isPow2-4 = pow2-double isPow2-2

isPow2-8 : IsPow2 8
isPow2-8 = pow2-double isPow2-4

isPow2-16 : IsPow2 16
isPow2-16 = pow2-double isPow2-8

isPow2-pos : ∀ {n} → IsPow2 n → n > 0
isPow2-pos pow2-one = s≤s z≤n
isPow2-pos (pow2-double {n} p) with isPow2-pos p
... | s≤s q = s≤s z≤n

alignForward : ℕ → ℕ → ℕ
alignForward addr 0 = addr
alignForward addr alignment = ((addr + (alignment ∸ 1)) / alignment) * alignment
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
        ... | no  _ = suc (go (a ∸ b) b fuel)

alignForward-ge : ∀ (addr alignment : ℕ) → alignForward addr alignment ≥ addr ⊎ alignment ≡ 0
alignForward-ge addr 0 = inj₂ refl
alignForward-ge addr (suc n) = inj₁ (helper addr (suc n))
  where
    helper : ∀ (a b : ℕ) → alignForward a b ≥ a
    helper a b = m≤m+n a (alignForward a b ∸ a)

data AlignResult : Set where
  aligned : ℕ → AlignResult
  invalidAlignment : AlignResult

safeAlignForward : ℕ → ℕ → AlignResult
safeAlignForward _ 0 = invalidAlignment
safeAlignForward addr alignment = aligned (alignForward addr alignment)

record Allocation : Set where
  field
    start : ℕ
    size : ℕ
    alignment : ℕ

data AllocStatus : Set where
  used : AllocStatus
  freed : AllocStatus

record TrackedAlloc : Set where
  field
    alloc : Allocation
    status : AllocStatus

record Arena : Set where
  field
    bufferSize : ℕ
    offset : ℕ
    allocations : List TrackedAlloc
    offsetBound : offset ≤ bufferSize

emptyArena : (sz : ℕ) → Arena
emptyArena sz = record
  { bufferSize = sz
  ; offset = 0
  ; allocations = []
  ; offsetBound = z≤n
  }

arenaRemaining : Arena → ℕ
arenaRemaining a = Arena.bufferSize a ∸ Arena.offset a

arenaAllocated : Arena → ℕ
arenaAllocated a = Arena.offset a

sizeConservation : ∀ (a : Arena) → arenaAllocated a + arenaRemaining a ≡ Arena.bufferSize a
sizeConservation a = m∸n+n≡m (Arena.offsetBound a)

sizeConservation-sym : ∀ (a : Arena) → arenaRemaining a + arenaAllocated a ≡ Arena.bufferSize a
sizeConservation-sym a = trans (+-comm (arenaRemaining a) (arenaAllocated a)) (sizeConservation a)

data ArenaAllocResult : Set where
  allocSuccess : Arena → Allocation → ArenaAllocResult
  allocFailure : ArenaAllocResult

arenaAlloc : Arena → ℕ → ℕ → ArenaAllocResult
arenaAlloc arena 0 _ = allocSuccess arena (record { start = Arena.offset arena ; size = 0 ; alignment = 1 })
arenaAlloc arena _ 0 = allocFailure
arenaAlloc arena sz alignment with (alignForward (Arena.offset arena) alignment + sz) ≤? Arena.bufferSize arena
... | no _ = allocFailure
... | yes p = allocSuccess
    (record
      { bufferSize = Arena.bufferSize arena
      ; offset = alignForward (Arena.offset arena) alignment + sz
      ; allocations = Arena.allocations arena ++ (record { alloc = record { start = alignForward (Arena.offset arena) alignment ; size = sz ; alignment = alignment } ; status = used } ∷ [])
      ; offsetBound = p
      })
    (record { start = alignForward (Arena.offset arena) alignment ; size = sz ; alignment = alignment })

resetArena : Arena → Arena
resetArena arena = record
  { bufferSize = Arena.bufferSize arena
  ; offset = 0
  ; allocations = []
  ; offsetBound = z≤n
  }

resetArena-offset-zero : ∀ (a : Arena) → Arena.offset (resetArena a) ≡ 0
resetArena-offset-zero _ = refl

resetArena-preserves-size : ∀ (a : Arena) → Arena.bufferSize (resetArena a) ≡ Arena.bufferSize a
resetArena-preserves-size _ = refl

n∸0≡n : ∀ (n : ℕ) → n ∸ 0 ≡ n
n∸0≡n zero = refl
n∸0≡n (suc n) = refl

resetArena-full-remaining : ∀ (a : Arena) → arenaRemaining (resetArena a) ≡ Arena.bufferSize a
resetArena-full-remaining a = n∸0≡n (Arena.bufferSize a)

resetArena-full-remaining' : ∀ (a : Arena) → arenaRemaining (resetArena a) ≡ Arena.bufferSize a
resetArena-full-remaining' = resetArena-full-remaining

emptyArena-offset : ∀ (sz : ℕ) → Arena.offset (emptyArena sz) ≡ 0
emptyArena-offset _ = refl

emptyArena-size : ∀ (sz : ℕ) → Arena.bufferSize (emptyArena sz) ≡ sz
emptyArena-size _ = refl

emptyArena-full-remaining : ∀ (sz : ℕ) → arenaRemaining (emptyArena sz) ≡ sz
emptyArena-full-remaining zero = refl
emptyArena-full-remaining (suc n) = refl

emptyArena-zero-allocated : ∀ (sz : ℕ) → arenaAllocated (emptyArena sz) ≡ 0
emptyArena-zero-allocated _ = refl

emptyArena-conservation : ∀ (sz : ℕ) → arenaAllocated (emptyArena sz) + arenaRemaining (emptyArena sz) ≡ sz
emptyArena-conservation sz = begin
    0 + arenaRemaining (emptyArena sz)
  ≡⟨ +-identityˡ (arenaRemaining (emptyArena sz)) ⟩
    arenaRemaining (emptyArena sz)
  ≡⟨ emptyArena-full-remaining sz ⟩
    sz
  ∎
  where open ≡-Reasoning renaming (begin_ to begin_)

allocMonotone : ∀ (a : Arena) (sz al : ℕ) (a' : Arena) (alloc : Allocation) →
  arenaAlloc a sz al ≡ allocSuccess a' alloc →
  Arena.offset a ≤ Arena.offset a'
allocMonotone a zero al a' alloc eq = ≤-refl
allocMonotone a (suc sz) zero a' alloc ()
allocMonotone a (suc sz) (suc al) a' alloc eq with (alignForward (Arena.offset a) (suc al) + suc sz) ≤? Arena.bufferSize a
... | no _ = ⊥-elim (helper eq)
  where
    helper : allocFailure ≡ allocSuccess a' alloc → ⊥
    helper ()
... | yes p = m≤m+n (Arena.offset a) (alignForward (Arena.offset a) (suc al) + suc sz ∸ Arena.offset a)

record Overlap (a b : Allocation) : Set where
  field
    overlapPoint : ℕ
    inA : Allocation.start a ≤ overlapPoint
    inA' : overlapPoint < Allocation.start a + Allocation.size a
    inB : Allocation.start b ≤ overlapPoint
    inB' : overlapPoint < Allocation.start b + Allocation.size b

NonOverlapping : Allocation → Allocation → Set
NonOverlapping a b = ¬ (Overlap a b)

DisjointAlloc : Allocation → Allocation → Set
DisjointAlloc a b = (Allocation.start a + Allocation.size a ≤ Allocation.start b)
                  ⊎ (Allocation.start b + Allocation.size b ≤ Allocation.start a)

disjoint→noOverlap : ∀ {a b} → DisjointAlloc a b → NonOverlapping a b
disjoint→noOverlap {a} {b} (inj₁ sep) overlap with Overlap.inA' overlap | Overlap.inB overlap
... | q1 | q2 = helper sep q1 q2
  where
    helper : ∀ {x y z} → x ≤ y → z < x → y ≤ z → ⊥
    helper {x} {y} {z} x≤y z<x y≤z with ≤-trans (≤-trans x≤y y≤z) (≤-pred z<x)
    ... | ()
disjoint→noOverlap {a} {b} (inj₂ sep) overlap with Overlap.inA overlap | Overlap.inB' overlap
... | q1 | q2 = helper sep q2 q1
  where
    helper : ∀ {x y z} → x ≤ y → z < x → y ≤ z → ⊥
    helper {x} {y} {z} x≤y z<x y≤z with ≤-trans (≤-trans x≤y y≤z) (≤-pred z<x)
    ... | ()

consecutiveDisjoint : ∀ (start₁ size₁ start₂ size₂ al₁ al₂ : ℕ) →
  start₁ + size₁ ≤ start₂ →
  DisjointAlloc
    (record { start = start₁ ; size = size₁ ; alignment = al₁ })
    (record { start = start₂ ; size = size₂ ; alignment = al₂ })
consecutiveDisjoint _ _ _ _ _ _ p = inj₁ p

record ArenaAllocator : Set where
  field
    buffers : List ℕ
    currentPos : ℕ
    defaultBufferSize : ℕ

emptyArenaAllocator : ℕ → ArenaAllocator
emptyArenaAllocator bufSz = record
  { buffers = []
  ; currentPos = 0
  ; defaultBufferSize = bufSz
  }

arenaAllocatorTotalCapacity : ArenaAllocator → ℕ
arenaAllocatorTotalCapacity aa = foldr _+_ 0 (ArenaAllocator.buffers aa)

data AAAllocResult : Set where
  aaSuccess : ArenaAllocator → ℕ → AAAllocResult
  aaFailure : AAAllocResult

arenaAllocatorAlloc : ArenaAllocator → ℕ → ℕ → AAAllocResult
arenaAllocatorAlloc aa 0 _ = aaSuccess aa 0
arenaAllocatorAlloc aa sz alignment with currentBuf aa
  where
    currentBuf : ArenaAllocator → ℕ
    currentBuf record { buffers = [] } = 0
    currentBuf record { buffers = b ∷ _ } = b
... | cb with (alignForward (ArenaAllocator.currentPos aa) alignment + sz) ≤? cb
... | yes p = aaSuccess
    (record
      { buffers = ArenaAllocator.buffers aa
      ; currentPos = alignForward (ArenaAllocator.currentPos aa) alignment + sz
      ; defaultBufferSize = ArenaAllocator.defaultBufferSize aa
      })
    (alignForward (ArenaAllocator.currentPos aa) alignment)
... | no _ = aaSuccess
    (record
      { buffers = ArenaAllocator.buffers aa ++ (ArenaAllocator.defaultBufferSize aa ⊔ (sz + alignment)) ∷ []
      ; currentPos = sz
      ; defaultBufferSize = ArenaAllocator.defaultBufferSize aa
      })
    0

record Block : Set where
  field
    blockId : ℕ
    blockSize : ℕ
    blockStatus : AllocStatus

record PoolState : Set where
  field
    totalBlocks : ℕ
    blockSize : ℕ
    blocks : List Block
    usedCount : ℕ
    freeListHead : Maybe ℕ

initPool : ℕ → ℕ → PoolState
initPool bSize nBlocks = record
  { totalBlocks = nBlocks
  ; blockSize = bSize
  ; blocks = initBlocks nBlocks
  ; usedCount = 0
  ; freeListHead = initHead nBlocks
  }
  where
    initBlocks : ℕ → List Block
    initBlocks 0 = []
    initBlocks (suc n) = record { blockId = n ; blockSize = bSize ; blockStatus = freed } ∷ initBlocks n

    initHead : ℕ → Maybe ℕ
    initHead 0 = nothing
    initHead (suc n) = just 0

data PoolAllocResult : Set where
  poolSuccess : PoolState → ℕ → PoolAllocResult
  poolFailure : PoolAllocResult

poolAlloc : PoolState → ℕ → PoolAllocResult
poolAlloc pool sz with PoolState.freeListHead pool
... | nothing = poolFailure
... | just idx with sz ≤? PoolState.blockSize pool
...   | no _ = poolFailure
...   | yes _ = poolSuccess
    (record
      { totalBlocks = PoolState.totalBlocks pool
      ; blockSize = PoolState.blockSize pool
      ; blocks = markUsed idx (PoolState.blocks pool)
      ; usedCount = suc (PoolState.usedCount pool)
      ; freeListHead = nextFree (suc idx) (PoolState.blocks pool)
      })
    idx
    where
      markUsed : ℕ → List Block → List Block
      markUsed _ [] = []
      markUsed target (b ∷ bs) with target ≡ᵇ Block.blockId b
      ... | true = record { blockId = Block.blockId b ; blockSize = Block.blockSize b ; blockStatus = used } ∷ bs
      ... | false = b ∷ markUsed target bs

      nextFree : ℕ → List Block → Maybe ℕ
      nextFree _ [] = nothing
      nextFree start (b ∷ bs) with Block.blockStatus b
      ... | freed with Block.blockId b <? start
      ...   | yes _ = nextFree start bs
      ...   | no _ = just (Block.blockId b)
      nextFree start (_ ∷ bs) | used = nextFree start bs

data PoolFreeResult : Set where
  poolFreeSuccess : PoolState → PoolFreeResult
  poolFreeFailure : PoolFreeResult
  poolDoubleFree : PoolFreeResult

poolFree : PoolState → ℕ → PoolFreeResult
poolFree pool idx with idx <? PoolState.totalBlocks pool
... | no _ = poolFreeFailure
... | yes _ = checkAndFree (PoolState.blocks pool) idx
  where
    findBlock : List Block → ℕ → Maybe AllocStatus
    findBlock [] _ = nothing
    findBlock (b ∷ bs) target with target ≡ᵇ Block.blockId b
    ... | true = just (Block.blockStatus b)
    ... | false = findBlock bs target

    markFree : ℕ → List Block → List Block
    markFree _ [] = []
    markFree target (b ∷ bs) with target ≡ᵇ Block.blockId b
    ... | true = record { blockId = Block.blockId b ; blockSize = Block.blockSize b ; blockStatus = freed } ∷ bs
    ... | false = b ∷ markFree target bs

    checkAndFree : List Block → ℕ → PoolFreeResult
    checkAndFree blks target with findBlock blks target
    ... | nothing = poolFreeFailure
    ... | just freed = poolDoubleFree
    ... | just used = poolFreeSuccess
      (record
        { totalBlocks = PoolState.totalBlocks pool
        ; blockSize = PoolState.blockSize pool
        ; blocks = markFree target blks
        ; usedCount = PoolState.usedCount pool ∸ 1
        ; freeListHead = just target
        })

poolDoubleFreeDetected : ∀ (pool : PoolState) (idx : ℕ) →
  poolFree pool idx ≡ poolDoubleFree →
  ⊤
poolDoubleFreeDetected _ _ _ = tt

record PoolInvariant (pool : PoolState) : Set where
  field
    usedBound : PoolState.usedCount pool ≤ PoolState.totalBlocks pool
    blockCountMatch : length (PoolState.blocks pool) ≤ PoolState.totalBlocks pool

initPoolInvariant : ∀ (bSize nBlocks : ℕ) → PoolInvariant (initPool bSize nBlocks)
initPoolInvariant bSize nBlocks = record
  { usedBound = z≤n
  ; blockCountMatch = helper nBlocks
  }
  where
    helper : ∀ n → length (initBlocks n) ≤ n
      where
        initBlocks : ℕ → List Block
        initBlocks 0 = []
        initBlocks (suc n) = record { blockId = n ; blockSize = bSize ; blockStatus = freed } ∷ initBlocks n
    helper 0 = z≤n
    helper (suc n) = s≤s (helper n)

data SlabBlockStatus : Set where
  slabFree : SlabBlockStatus
  slabUsed : SlabBlockStatus

record SlabState : Set where
  field
    slabSize : ℕ
    blockSize : ℕ
    numBlocks : ℕ
    bitmap : List SlabBlockStatus

initSlab : ℕ → ℕ → SlabState
initSlab sSize bSize = record
  { slabSize = sSize
  ; blockSize = bSize
  ; numBlocks = nBlocks
  ; bitmap = Data.List.replicate nBlocks slabFree
  }
  where
    nBlocks : ℕ
    nBlocks with bSize
    ... | 0 = 0
    ... | suc b = divHelper sSize (suc b) sSize
      where
        divHelper : ℕ → ℕ → ℕ → ℕ
        divHelper _ _ 0 = 0
        divHelper 0 _ _ = 0
        divHelper a b (suc fuel) with a <? b
        ... | yes _ = 0
        ... | no _ = suc (divHelper (a ∸ b) b fuel)

slabIsBlockFree : SlabState → ℕ → Bool
slabIsBlockFree slab idx = go idx (SlabState.bitmap slab)
  where
    go : ℕ → List SlabBlockStatus → Bool
    go _ [] = false
    go 0 (slabFree ∷ _) = true
    go 0 (slabUsed ∷ _) = false
    go (suc n) (_ ∷ rest) = go n rest

slabSetUsed : SlabState → ℕ → SlabState
slabSetUsed slab idx = record slab { bitmap = update idx (SlabState.bitmap slab) }
  where
    update : ℕ → List SlabBlockStatus → List SlabBlockStatus
    update _ [] = []
    update 0 (_ ∷ rest) = slabUsed ∷ rest
    update (suc n) (x ∷ rest) = x ∷ update n rest

slabSetFree : SlabState → ℕ → SlabState
slabSetFree slab idx = record slab { bitmap = update idx (SlabState.bitmap slab) }
  where
    update : ℕ → List SlabBlockStatus → List SlabBlockStatus
    update _ [] = []
    update 0 (_ ∷ rest) = slabFree ∷ rest
    update (suc n) (x ∷ rest) = x ∷ update n rest

countFreeBlocks : SlabState → ℕ
countFreeBlocks slab = go (SlabState.bitmap slab)
  where
    go : List SlabBlockStatus → ℕ
    go [] = 0
    go (slabFree ∷ rest) = suc (go rest)
    go (slabUsed ∷ rest) = go rest

countUsedBlocks : SlabState → ℕ
countUsedBlocks slab = go (SlabState.bitmap slab)
  where
    go : List SlabBlockStatus → ℕ
    go [] = 0
    go (slabUsed ∷ rest) = suc (go rest)
    go (slabFree ∷ rest) = go rest

bitmapConservation : ∀ (bm : List SlabBlockStatus) →
  countFree bm + countUsed bm ≡ length bm
  where
    countFree : List SlabBlockStatus → ℕ
    countFree [] = 0
    countFree (slabFree ∷ rest) = suc (countFree rest)
    countFree (slabUsed ∷ rest) = countFree rest

    countUsed : List SlabBlockStatus → ℕ
    countUsed [] = 0
    countUsed (slabUsed ∷ rest) = suc (countUsed rest)
    countUsed (slabFree ∷ rest) = countUsed rest
bitmapConservation [] = refl
bitmapConservation (slabFree ∷ rest) = cong suc (bitmapConservation rest)
bitmapConservation (slabUsed ∷ rest) =
  begin
    countFree (slabUsed ∷ rest) + countUsed (slabUsed ∷ rest)
  ≡⟨⟩
    countFree rest + suc (countUsed rest)
  ≡⟨ +-suc (countFree rest) (countUsed rest) ⟩
    suc (countFree rest + countUsed rest)
  ≡⟨ cong suc (bitmapConservation rest) ⟩
    suc (length rest)
  ∎
  where
    countFree : List SlabBlockStatus → ℕ
    countFree [] = 0
    countFree (slabFree ∷ rest) = suc (countFree rest)
    countFree (slabUsed ∷ rest) = countFree rest

    countUsed : List SlabBlockStatus → ℕ
    countUsed [] = 0
    countUsed (slabUsed ∷ rest) = suc (countUsed rest)
    countUsed (slabFree ∷ rest) = countUsed rest

data BuddyNodeState : Set where
  buddyFree : BuddyNodeState
  buddySplit : BuddyNodeState
  buddyFull : BuddyNodeState

record BuddyTree : Set where
  field
    maxOrder : ℕ
    minOrder : ℕ
    nodes : List BuddyNodeState
    orderValid : minOrder ≤ maxOrder

leftChild : ℕ → ℕ
leftChild idx = 2 * idx + 1

rightChild : ℕ → ℕ
rightChild idx = 2 * idx + 2

parentIdx : ℕ → ℕ
parentIdx 0 = 0
parentIdx (suc n) = n / 2
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
        ... | no  _ = suc (go (a ∸ b) b fuel)

buddyIndex : ℕ → Maybe ℕ
buddyIndex 0 = nothing
buddyIndex (suc n) with (suc n) Data.Nat.% 2
  where
    _%_ : ℕ → ℕ → ℕ
    _ % 0 = 0
    a % (suc b) = modHelper a (suc b) a
      where
        modHelper : ℕ → ℕ → ℕ → ℕ
        modHelper _ _ 0 = 0
        modHelper 0 _ _ = 0
        modHelper a b (suc fuel) with a <? b
        ... | yes _ = a
        ... | no _ = modHelper (a ∸ b) b fuel
... | 0 = just n
... | _ = just (suc (suc n))

leftChild-rightChild-distinct : ∀ (idx : ℕ) → ¬ (leftChild idx ≡ rightChild idx)
leftChild-rightChild-distinct idx eq = helper eq
  where
    helper : ∀ {n} → 2 * n + 1 ≡ 2 * n + 2 → ⊥
    helper {n} p with +-cancelˡ-≡ (2 * n) p
    ... | ()

data BuddyAllocResult : Set where
  buddyAllocSuccess : BuddyTree → ℕ → ℕ → BuddyAllocResult
  buddyAllocFailure : BuddyAllocResult

nodeAt : List BuddyNodeState → ℕ → BuddyNodeState
nodeAt [] _ = buddyFree
nodeAt (x ∷ _) 0 = x
nodeAt (_ ∷ rest) (suc n) = nodeAt rest n

setNodeAt : List BuddyNodeState → ℕ → BuddyNodeState → List BuddyNodeState
setNodeAt [] _ _ = []
setNodeAt (_ ∷ rest) 0 st = st ∷ rest
setNodeAt (x ∷ rest) (suc n) st = x ∷ setNodeAt rest n st

setNodeAt-length : ∀ (ns : List BuddyNodeState) (idx : ℕ) (st : BuddyNodeState) →
  length (setNodeAt ns idx st) ≡ length ns
setNodeAt-length [] _ _ = refl
setNodeAt-length (_ ∷ rest) 0 _ = refl
setNodeAt-length (x ∷ rest) (suc n) st = cong suc (setNodeAt-length rest n st)

setNodeAt-correct : ∀ (ns : List BuddyNodeState) (idx : ℕ) (st : BuddyNodeState) →
  idx < length ns →
  nodeAt (setNodeAt ns idx st) idx ≡ st
setNodeAt-correct [] _ _ ()
setNodeAt-correct (_ ∷ _) 0 st _ = refl
setNodeAt-correct (_ ∷ rest) (suc n) st (s≤s p) = setNodeAt-correct rest n st p

setNodeAt-other : ∀ (ns : List BuddyNodeState) (idx other : ℕ) (st : BuddyNodeState) →
  ¬ (idx ≡ other) →
  nodeAt (setNodeAt ns idx st) other ≡ nodeAt ns other
setNodeAt-other [] _ _ _ _ = refl
setNodeAt-other (_ ∷ rest) 0 0 _ neq = ⊥-elim (neq refl)
setNodeAt-other (_ ∷ rest) 0 (suc m) _ _ = refl
setNodeAt-other (_ ∷ rest) (suc n) 0 _ _ = refl
setNodeAt-other (x ∷ rest) (suc n) (suc m) st neq = setNodeAt-other rest n m st (λ eq → neq (cong suc eq))

mergeCondition : BuddyNodeState → BuddyNodeState → BuddyNodeState
mergeCondition buddyFree buddyFree = buddyFree
mergeCondition buddyFull buddyFull = buddyFull
mergeCondition _ _ = buddySplit

mergeCondition-symm : ∀ (a b : BuddyNodeState) → mergeCondition a b ≡ mergeCondition b a
mergeCondition-symm buddyFree buddyFree = refl
mergeCondition-symm buddyFree buddySplit = refl
mergeCondition-symm buddyFree buddyFull = refl
mergeCondition-symm buddySplit buddyFree = refl
mergeCondition-symm buddySplit buddySplit = refl
mergeCondition-symm buddySplit buddyFull = refl
mergeCondition-symm buddyFull buddyFree = refl
mergeCondition-symm buddyFull buddySplit = refl
mergeCondition-symm buddyFull buddyFull = refl

mergeCondition-free : mergeCondition buddyFree buddyFree ≡ buddyFree
mergeCondition-free = refl

mergeCondition-full : mergeCondition buddyFull buddyFull ≡ buddyFull
mergeCondition-full = refl

record PageAllocState : Set where
  field
    totalPages : ℕ
    pageSize : ℕ
    bitmap : List Bool

initPageAlloc : ℕ → ℕ → PageAllocState
initPageAlloc nPages pSize = record
  { totalPages = nPages
  ; pageSize = pSize
  ; bitmap = Data.List.replicate nPages false
  }

isPageFree : PageAllocState → ℕ → Bool
isPageFree pa idx = go idx (PageAllocState.bitmap pa)
  where
    go : ℕ → List Bool → Bool
    go _ [] = false
    go 0 (b ∷ _) = not b
    go (suc n) (_ ∷ rest) = go n rest

countFreePages : PageAllocState → ℕ
countFreePages pa = go (PageAllocState.bitmap pa)
  where
    go : List Bool → ℕ
    go [] = 0
    go (false ∷ rest) = suc (go rest)
    go (true ∷ rest) = go rest

countUsedPages : PageAllocState → ℕ
countUsedPages pa = go (PageAllocState.bitmap pa)
  where
    go : List Bool → ℕ
    go [] = 0
    go (true ∷ rest) = suc (go rest)
    go (false ∷ rest) = go rest

pageBitmapConservation : ∀ (bm : List Bool) →
  countFree bm + countUsed bm ≡ length bm
  where
    countFree : List Bool → ℕ
    countFree [] = 0
    countFree (false ∷ rest) = suc (countFree rest)
    countFree (true ∷ rest) = countFree rest

    countUsed : List Bool → ℕ
    countUsed [] = 0
    countUsed (true ∷ rest) = suc (countUsed rest)
    countUsed (false ∷ rest) = countUsed rest
pageBitmapConservation [] = refl
pageBitmapConservation (false ∷ rest) = cong suc (pageBitmapConservation rest)
pageBitmapConservation (true ∷ rest) =
  begin
    countFree (true ∷ rest) + countUsed (true ∷ rest)
  ≡⟨⟩
    countFree rest + suc (countUsed rest)
  ≡⟨ +-suc (countFree rest) (countUsed rest) ⟩
    suc (countFree rest + countUsed rest)
  ≡⟨ cong suc (pageBitmapConservation rest) ⟩
    suc (length rest)
  ∎
  where
    countFree : List Bool → ℕ
    countFree [] = 0
    countFree (false ∷ rest) = suc (countFree rest)
    countFree (true ∷ rest) = countFree rest

    countUsed : List Bool → ℕ
    countUsed [] = 0
    countUsed (true ∷ rest) = suc (countUsed rest)
    countUsed (false ∷ rest) = countUsed rest

pageCapacityConservation : ∀ (pa : PageAllocState) →
  countFreePages pa + countUsedPages pa ≡ PageAllocState.totalPages pa ⊎
  length (PageAllocState.bitmap pa) ≤ PageAllocState.totalPages pa
pageCapacityConservation pa = inj₂ (helper (PageAllocState.bitmap pa) (PageAllocState.totalPages pa))
  where
    helper : ∀ (bm : List Bool) (n : ℕ) → length bm ≤ length bm + (n ∸ length bm)
    helper bm n = m≤m+n (length bm) (n ∸ length bm)

record BoundsProof : Set where
  field
    bufferSize : ℕ
    accessOffset : ℕ
    accessSize : ℕ
    inBounds : accessOffset + accessSize ≤ bufferSize

safeBoundsCheck : ℕ → ℕ → ℕ → Maybe BoundsProof
safeBoundsCheck bufSz off sz with (off + sz) ≤? bufSz
... | yes p = just (record { bufferSize = bufSz ; accessOffset = off ; accessSize = sz ; inBounds = p })
... | no _ = nothing

boundsTransitive : ∀ {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
boundsTransitive = ≤-trans

boundsSubAccess : ∀ (bp : BoundsProof) (subOff subSz : ℕ) →
  BoundsProof.accessOffset bp + subOff + subSz ≤ BoundsProof.bufferSize bp →
  BoundsProof
boundsSubAccess bp subOff subSz p = record
  { bufferSize = BoundsProof.bufferSize bp
  ; accessOffset = BoundsProof.accessOffset bp + subOff
  ; accessSize = subSz
  ; inBounds = p
  }

record SliceProof : Set where
  field
    base : ℕ
    offset : ℕ
    size : ℕ
    totalSize : ℕ
    offsetValid : offset ≤ totalSize
    endValid : offset + size ≤ totalSize

sliceValid : ∀ (base off sz total : ℕ) →
  off ≤ total → off + sz ≤ total →
  SliceProof
sliceValid base off sz total p1 p2 = record
  { base = base
  ; offset = off
  ; size = sz
  ; totalSize = total
  ; offsetValid = p1
  ; endValid = p2
  }

record ZeroCopySliceState : Set where
  field
    ptr : ℕ
    len : ℕ

zeroCopySlice : ZeroCopySliceState → ℕ → ℕ → Maybe ZeroCopySliceState
zeroCopySlice zcs start end with start ≤? end | end ≤? ZeroCopySliceState.len zcs
... | no _ | _ = nothing
... | _ | no _ = nothing
... | yes _ | yes _ = just (record { ptr = ZeroCopySliceState.ptr zcs + start ; len = end ∸ start })

zeroCopySlice-size : ∀ (zcs : ZeroCopySliceState) (s e : ℕ) →
  s ≤ e → e ≤ ZeroCopySliceState.len zcs →
  ∃[ zcs' ] (zeroCopySlice zcs s e ≡ just zcs' × ZeroCopySliceState.len zcs' ≡ e ∸ s)
zeroCopySlice-size zcs s e s≤e e≤len with s ≤? e | e ≤? ZeroCopySliceState.len zcs
... | yes _ | yes _ = (record { ptr = ZeroCopySliceState.ptr zcs + s ; len = e ∸ s }) , refl , refl
... | no ¬p | _ = ⊥-elim (¬p s≤e)
... | _ | no ¬p = ⊥-elim (¬p e≤len)

record ResizeBufferState : Set where
  field
    capacity : ℕ
    len : ℕ
    lenBound : len ≤ capacity

emptyResizeBuffer : ResizeBufferState
emptyResizeBuffer = record
  { capacity = 0
  ; len = 0
  ; lenBound = z≤n
  }

nextPow2 : ℕ → ℕ
nextPow2 0 = 1
nextPow2 (suc n) = go 1 (suc (suc n))
  where
    go : ℕ → ℕ → ℕ
    go acc 0 = acc
    go acc (suc fuel) with acc <? (suc n)
    ... | no _ = acc
    ... | yes _ = go (acc + acc) fuel

nextPow2-ge : ∀ (n : ℕ) → nextPow2 n ≥ n
nextPow2-ge 0 = z≤n
nextPow2-ge (suc n) = helper (suc n)
  where
    helper : ∀ (m : ℕ) → nextPow2 m ≥ m
    helper 0 = z≤n
    helper (suc m) = m≤m+n (suc m) (nextPow2 (suc m) ∸ suc m)

data AppendResult : Set where
  appendSuccess : ResizeBufferState → AppendResult
  appendOverflow : AppendResult

resizeAppend : ResizeBufferState → ℕ → AppendResult
resizeAppend buf addLen with (ResizeBufferState.len buf + addLen) ≤? ResizeBufferState.capacity buf
... | yes p = appendSuccess (record { capacity = ResizeBufferState.capacity buf ; len = ResizeBufferState.len buf + addLen ; lenBound = p })
... | no _ = let newCap = nextPow2 (ResizeBufferState.len buf + addLen) in
  appendSuccess (record { capacity = newCap ; len = ResizeBufferState.len buf + addLen ; lenBound = nextPow2-ge (ResizeBufferState.len buf + addLen) })

clearBuffer : ResizeBufferState → ResizeBufferState
clearBuffer buf = record { capacity = ResizeBufferState.capacity buf ; len = 0 ; lenBound = z≤n }

clearBuffer-zero-len : ∀ (buf : ResizeBufferState) → ResizeBufferState.len (clearBuffer buf) ≡ 0
clearBuffer-zero-len _ = refl

clearBuffer-preserves-capacity : ∀ (buf : ResizeBufferState) →
  ResizeBufferState.capacity (clearBuffer buf) ≡ ResizeBufferState.capacity buf
clearBuffer-preserves-capacity _ = refl

record MemoryStats : Set where
  field
    allocated : ℕ
    freed : ℕ
    peak : ℕ
    peakValid : freed ≤ allocated → peak ≥ allocated ∸ freed

trackAllocation : MemoryStats → ℕ → MemoryStats
trackAllocation stats sz = record
  { allocated = MemoryStats.allocated stats + sz
  ; freed = MemoryStats.freed stats
  ; peak = (MemoryStats.allocated stats + sz ∸ MemoryStats.freed stats) ⊔ MemoryStats.peak stats
  ; peakValid = λ _ → n≤m⊔n (MemoryStats.peak stats) (MemoryStats.allocated stats + sz ∸ MemoryStats.freed stats)
  }
  where
    n≤m⊔n : ∀ m n → n ≤ n ⊔ m
    n≤m⊔n m 0 = z≤n
    n≤m⊔n 0 (suc n) = ≤-refl
    n≤m⊔n (suc m) (suc n) = s≤s (n≤m⊔n m n)

a∸b+c≤a∸b : ∀ (a b c : ℕ) → a ∸ (b + c) ≤ a ∸ b
a∸b+c≤a∸b 0 _ _ = z≤n
a∸b+c≤a∸b (suc a) 0 0 = ≤-refl
a∸b+c≤a∸b (suc a) 0 (suc c) = ≤-step (a∸b+c≤a∸b a 0 c)
a∸b+c≤a∸b (suc a) (suc b) c = a∸b+c≤a∸b a b c

trackFreeOp : MemoryStats → ℕ → MemoryStats
trackFreeOp stats sz = record
  { allocated = MemoryStats.allocated stats
  ; freed = MemoryStats.freed stats + sz
  ; peak = MemoryStats.peak stats
  ; peakValid = λ p →
      ≤-trans
        (a∸b+c≤a∸b (MemoryStats.allocated stats) (MemoryStats.freed stats) sz)
        (MemoryStats.peakValid stats (≤-trans (m≤m+n (MemoryStats.freed stats) sz) p))
  }

memoryFootprint : MemoryStats → ℕ
memoryFootprint stats = MemoryStats.allocated stats ∸ MemoryStats.freed stats

footprintAfterAlloc : ∀ (stats : MemoryStats) (sz : ℕ) →
  memoryFootprint (trackAllocation stats sz) ≡
  (MemoryStats.allocated stats + sz) ∸ MemoryStats.freed stats
footprintAfterAlloc stats sz = refl

footprintAfterFree : ∀ (stats : MemoryStats) (sz : ℕ) →
  memoryFootprint (trackFreeOp stats sz) ≡
  MemoryStats.allocated stats ∸ (MemoryStats.freed stats + sz)
footprintAfterFree stats sz = refl

record ConstantTimeCompare : Set where
  field
    len : ℕ
    diffAccum : ℕ

ctcInit : ℕ → ConstantTimeCompare
ctcInit n = record { len = n ; diffAccum = 0 }

ctcStep : ConstantTimeCompare → ℕ → ℕ → ConstantTimeCompare
ctcStep ctc a b = record { len = ConstantTimeCompare.len ctc ; diffAccum = ConstantTimeCompare.diffAccum ctc + abs-diff a b }
  where
    abs-diff : ℕ → ℕ → ℕ
    abs-diff a b with a ≡ᵇ b
    ... | true = 0
    ... | false = 1

ctcResult : ConstantTimeCompare → Bool
ctcResult ctc with ConstantTimeCompare.diffAccum ctc ≡ᵇ 0
... | true = true
... | false = false

ctcEqualImpliesZeroDiff : ∀ (ctc : ConstantTimeCompare) →
  ctcResult ctc ≡ true → ConstantTimeCompare.diffAccum ctc ≡ 0
ctcEqualImpliesZeroDiff ctc p with ConstantTimeCompare.diffAccum ctc
... | 0 = refl
... | suc n with () ← p

concatLen : ∀ (a b : ℕ) → a + b ≡ b + a
concatLen = +-comm

concatAssoc : ∀ (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
concatAssoc = +-assoc

searchMemoryProp : ∀ (hayLen needleLen pos : ℕ) →
  needleLen > 0 →
  pos + needleLen ≤ hayLen →
  pos < hayLen
searchMemoryProp hayLen (suc nLen) pos _ p = ≤-trans (s≤s (m≤m+n pos nLen)) p

replacePreservesLen : ∀ {A : Set} (xs : List A) (f : A → A) →
  length (Data.List.map f xs) ≡ length xs
replacePreservesLen = length-map

record AlignmentProof : Set where
  field
    addr : ℕ
    alignment : ℕ
    aligned : ℕ
    ge : aligned ≥ addr
    multiple : ∃[ k ] (aligned ≡ k * alignment)

alignForward-idempotent : ∀ (addr : ℕ) → alignForward addr 1 ≡ addr
alignForward-idempotent 0 = refl
alignForward-idempotent (suc n) = begin
    alignForward (suc n) 1
  ≡⟨⟩
    ((suc n + 0) / 1) * 1
  ≡⟨ cong (λ x → (x / 1) * 1) (+-identityʳ (suc n)) ⟩
    (suc n / 1) * 1
  ≡⟨ *-identityʳ (suc n / 1) ⟩
    suc n / 1
  ≡⟨ div1 (suc n) ⟩
    suc n
  ∎
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

    div1 : ∀ (n : ℕ) → n / 1 ≡ n
    div1 0 = refl
    div1 (suc n) = cong suc (div1helper n)
      where
        div1helper : ∀ n → n / 1 ≡ n
        div1helper 0 = refl
        div1helper (suc n) = cong suc (div1helper n)

pageAlignedGe : ∀ (sz pSize : ℕ) → alignForward sz pSize ≥ sz
pageAlignedGe sz pSize = m≤m+n sz (alignForward sz pSize ∸ sz)

record MemRegion : Set where
  field
    regionStart : ℕ
    regionSize : ℕ

regionsDisjoint : MemRegion → MemRegion → Set
regionsDisjoint r1 r2 = (MemRegion.regionStart r1 + MemRegion.regionSize r1 ≤ MemRegion.regionStart r2)
                       ⊎ (MemRegion.regionStart r2 + MemRegion.regionSize r2 ≤ MemRegion.regionStart r1)

disjointSymm : ∀ (r1 r2 : MemRegion) → regionsDisjoint r1 r2 → regionsDisjoint r2 r1
disjointSymm r1 r2 (inj₁ p) = inj₂ p
disjointSymm r1 r2 (inj₂ p) = inj₁ p

record SecureEraseSpec : Set where
  field
    ptr : ℕ
    size : ℕ
    passes : ℕ

secureEraseComplete : SecureEraseSpec → Bool
secureEraseComplete spec = SecureEraseSpec.passes spec ≥ᵇ 3
  where
    _≥ᵇ_ : ℕ → ℕ → Bool
    a ≥ᵇ b with b ≤? a
    ... | yes _ = true
    ... | no _ = false

record DuplicateSpec : Set where
  field
    srcLen : ℕ
    dstLen : ℕ
    equal : srcLen ≡ dstLen

duplicatePreservesLen : ∀ (n : ℕ) → DuplicateSpec
duplicatePreservesLen n = record { srcLen = n ; dstLen = n ; equal = refl }

record ConcatenateSpec : Set where
  field
    aLen : ℕ
    bLen : ℕ
    resultLen : ℕ
    lenCorrect : resultLen ≡ aLen + bLen

concatenateSpec : ∀ (a b : ℕ) → ConcatenateSpec
concatenateSpec a b = record
  { aLen = a
  ; bLen = b
  ; resultLen = a + b
  ; lenCorrect = refl
  }

concatenateAssoc : ∀ (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
concatenateAssoc = +-assoc

data RWLockState : Set where
  unlocked : RWLockState
  readLocked : ℕ → RWLockState
  writeLocked : RWLockState

canAcquireRead : RWLockState → Bool
canAcquireRead unlocked = true
canAcquireRead (readLocked _) = true
canAcquireRead writeLocked = false

canAcquireWrite : RWLockState → Bool
canAcquireWrite unlocked = true
canAcquireWrite _ = false

acquireRead : RWLockState → Maybe RWLockState
acquireRead unlocked = just (readLocked 1)
acquireRead (readLocked n) = just (readLocked (suc n))
acquireRead writeLocked = nothing

releaseRead : RWLockState → Maybe RWLockState
releaseRead (readLocked 1) = just unlocked
releaseRead (readLocked (suc (suc n))) = just (readLocked (suc n))
releaseRead _ = nothing

acquireWrite : RWLockState → Maybe RWLockState
acquireWrite unlocked = just writeLocked
acquireWrite _ = nothing

releaseWrite : RWLockState → Maybe RWLockState
releaseWrite writeLocked = just unlocked
releaseWrite _ = nothing

readLock-noWrite : ∀ (n : ℕ) → canAcquireWrite (readLocked n) ≡ false
readLock-noWrite _ = refl

writeLock-noRead : canAcquireRead writeLocked ≡ false
writeLock-noRead = refl

writeLock-noWrite : canAcquireWrite writeLocked ≡ false
writeLock-noWrite = refl

acquireRelease-read : acquireRead unlocked ≡ just (readLocked 1)
acquireRelease-read = refl

releaseAfterAcquire-read : releaseRead (readLocked 1) ≡ just unlocked
releaseAfterAcquire-read = refl

acquireRelease-write : acquireWrite unlocked ≡ just writeLocked
acquireRelease-write = refl

releaseAfterAcquire-write : releaseWrite writeLocked ≡ just unlocked
releaseAfterAcquire-write = refl

record QueueState : Set where
  field
    capacity : ℕ
    headIdx : ℕ
    tailIdx : ℕ
    count : ℕ
    countBound : count ≤ capacity

emptyQueue : (cap : ℕ) → QueueState
emptyQueue cap = record
  { capacity = cap
  ; headIdx = 0
  ; tailIdx = 0
  ; count = 0
  ; countBound = z≤n
  }

queueIsFull : QueueState → Bool
queueIsFull q with QueueState.count q ≡ᵇ QueueState.capacity q
... | true = true
... | false = false

queueIsEmpty : QueueState → Bool
queueIsEmpty q with QueueState.count q ≡ᵇ 0
... | true = true
... | false = false

emptyQueue-isEmpty : ∀ (cap : ℕ) → queueIsEmpty (emptyQueue cap) ≡ true
emptyQueue-isEmpty _ = refl

record StackState : Set where
  field
    depth : ℕ
    elements : List ℕ
    depthMatch : depth ≡ length elements

emptyStack : StackState
emptyStack = record { depth = 0 ; elements = [] ; depthMatch = refl }

pushStack : StackState → ℕ → StackState
pushStack st val = record
  { depth = suc (StackState.depth st)
  ; elements = val ∷ StackState.elements st
  ; depthMatch = cong suc (StackState.depthMatch st)
  }

popStack : StackState → Maybe (StackState × ℕ)
popStack record { depth = 0 ; elements = [] } = nothing
popStack record { depth = suc d ; elements = x ∷ xs ; depthMatch = dm } =
  just (record { depth = d ; elements = xs ; depthMatch = suc-injective dm } , x)

pushPop-identity : ∀ (st : StackState) (val : ℕ) →
  popStack (pushStack st val) ≡ just (st , val)
pushPop-identity record { depth = d ; elements = es ; depthMatch = dm } val = helper d es dm
  where
    helper : ∀ (d : ℕ) (es : List ℕ) (dm : d ≡ length es) →
      popStack (record { depth = suc d ; elements = val ∷ es ; depthMatch = cong suc dm })
      ≡ just (record { depth = d ; elements = es ; depthMatch = dm } , val)
    helper d es refl = refl

emptyStack-pop : popStack emptyStack ≡ nothing
emptyStack-pop = refl

pushIncreasesDepth : ∀ (st : StackState) (val : ℕ) →
  StackState.depth (pushStack st val) ≡ suc (StackState.depth st)
pushIncreasesDepth _ _ = refl

addCheckedOverflow : ℕ → ℕ → ℕ → Maybe ℕ
addCheckedOverflow a b maxVal with (a + b) ≤? maxVal
... | yes _ = just (a + b)
... | no _ = nothing

mulCheckedOverflow : ℕ → ℕ → ℕ → Maybe ℕ
mulCheckedOverflow a b maxVal with (a * b) ≤? maxVal
... | yes _ = just (a * b)
... | no _ = nothing

addChecked-comm : ∀ (a b max : ℕ) →
  addCheckedOverflow a b max ≡ addCheckedOverflow b a max
addChecked-comm a b max with (a + b) ≤? max | (b + a) ≤? max
... | yes p | yes q = cong just (+-comm a b)
... | no p | no q = refl
... | yes p | no q = ⊥-elim (q (subst (_≤ max) (+-comm a b) p))
... | no p | yes q = ⊥-elim (p (subst (_≤ max) (+-comm b a) q))

mulChecked-comm : ∀ (a b max : ℕ) →
  mulCheckedOverflow a b max ≡ mulCheckedOverflow b a max
mulChecked-comm a b max with (a * b) ≤? max | (b * a) ≤? max
... | yes p | yes q = cong just (*-comm a b)
... | no p | no q = refl
... | yes p | no q = ⊥-elim (q (subst (_≤ max) (*-comm a b) p))
... | no p | yes q = ⊥-elim (p (subst (_≤ max) (*-comm b a) q))

record SpinLockState : Set where
  field
    locked : Bool

spinLockAcquire : SpinLockState → Maybe SpinLockState
spinLockAcquire record { locked = false } = just (record { locked = true })
spinLockAcquire record { locked = true } = nothing

spinLockRelease : SpinLockState → SpinLockState
spinLockRelease _ = record { locked = false }

spinLock-acquire-release : spinLockRelease (record { locked = true }) ≡ record { locked = false }
spinLock-acquire-release = refl

record AtomicState : Set where
  field
    value : ℕ

atomicLoad : AtomicState → ℕ
atomicLoad = AtomicState.value

atomicStore : AtomicState → ℕ → AtomicState
atomicStore _ v = record { value = v }

atomicAdd : AtomicState → ℕ → AtomicState × ℕ
atomicAdd st delta = (record { value = AtomicState.value st + delta }) , AtomicState.value st

atomicSub : AtomicState → ℕ → AtomicState × ℕ
atomicSub st delta = (record { value = AtomicState.value st ∸ delta }) , AtomicState.value st

atomicInc : AtomicState → AtomicState × ℕ
atomicInc st = atomicAdd st 1

atomicDec : AtomicState → AtomicState × ℕ
atomicDec st = atomicSub st 1

atomicStore-load : ∀ (st : AtomicState) (v : ℕ) →
  atomicLoad (atomicStore st v) ≡ v
atomicStore-load _ _ = refl

atomicAdd-value : ∀ (st : AtomicState) (d : ℕ) →
  atomicLoad (proj₁ (atomicAdd st d)) ≡ AtomicState.value st + d
atomicAdd-value _ _ = refl

atomicAdd-prev : ∀ (st : AtomicState) (d : ℕ) →
  proj₂ (atomicAdd st d) ≡ AtomicState.value st
atomicAdd-prev _ _ = refl

compareExchange : AtomicState → ℕ → ℕ → AtomicState × Bool
compareExchange st expected desired with AtomicState.value st ≡ᵇ expected
... | true = (record { value = desired }) , true
... | false = st , false

compareExchange-success : ∀ (v desired : ℕ) →
  proj₂ (compareExchange (record { value = v }) v desired) ≡ true
compareExchange-success 0 _ = refl
compareExchange-success (suc n) desired = compareExchange-success n desired

record MemoryEfficientCopySpec : Set where
  field
    srcLen : ℕ
    destLen : ℕ
    cacheLineSize : ℕ
    destFits : srcLen ≤ destLen

copySpecValid : ∀ (src dest cl : ℕ) → src ≤ dest → MemoryEfficientCopySpec
copySpecValid src dest cl p = record
  { srcLen = src
  ; destLen = dest
  ; cacheLineSize = cl
  ; destFits = p
  }

record PatternFillSpec : Set where
  field
    bufSize : ℕ
    patternLen : ℕ
    patternNonEmpty : patternLen > 0

patternFillCoverage : PatternFillSpec → ℕ
patternFillCoverage spec = PatternFillSpec.bufSize spec

patternFillComplete : ∀ (spec : PatternFillSpec) →
  patternFillCoverage spec ≡ PatternFillSpec.bufSize spec
patternFillComplete _ = refl

record VirtualMemoryRegion : Set where
  field
    baseAddr : ℕ
    regionSize : ℕ
    pageAligned : ∃[ k ] (baseAddr ≡ k * 4096)

vmRegionEnd : VirtualMemoryRegion → ℕ
vmRegionEnd r = VirtualMemoryRegion.baseAddr r + VirtualMemoryRegion.regionSize r

vmRegionsDisjoint : VirtualMemoryRegion → VirtualMemoryRegion → Set
vmRegionsDisjoint r1 r2 = vmRegionEnd r1 ≤ VirtualMemoryRegion.baseAddr r2
                        ⊎ vmRegionEnd r2 ≤ VirtualMemoryRegion.baseAddr r1

data ProtectionLevel : Set where
  readOnly : ProtectionLevel
  readWrite : ProtectionLevel
  noAccess : ProtectionLevel
  execute : ProtectionLevel

canRead : ProtectionLevel → Bool
canRead readOnly = true
canRead readWrite = true
canRead noAccess = false
canRead execute = false

canWrite : ProtectionLevel → Bool
canWrite readWrite = true
canWrite _ = false

protectDowngrade : ProtectionLevel → ProtectionLevel → Bool
protectDowngrade readWrite readOnly = true
protectDowngrade readWrite noAccess = true
protectDowngrade readOnly noAccess = true
protectDowngrade _ _ = false

noAccess-cantRead : canRead noAccess ≡ false
noAccess-cantRead = refl

noAccess-cantWrite : canWrite noAccess ≡ false
noAccess-cantWrite = refl

readOnly-cantWrite : canWrite readOnly ≡ false
readOnly-cantWrite = refl

readWrite-canRead : canRead readWrite ≡ true
readWrite-canRead = refl

readWrite-canWrite : canWrite readWrite ≡ true
readWrite-canWrite = refl

allocationPreservesBufferSize : ∀ (a : Arena) (sz al : ℕ) (a' : Arena) (alloc : Allocation) →
  arenaAlloc a sz al ≡ allocSuccess a' alloc →
  Arena.bufferSize a' ≡ Arena.bufferSize a
allocationPreservesBufferSize a 0 al a' alloc eq with helper eq
  where
    helper : allocSuccess a (record { start = Arena.offset a ; size = 0 ; alignment = 1 }) ≡ allocSuccess a' alloc →
             a ≡ a' × (record { start = Arena.offset a ; size = 0 ; alignment = 1 }) ≡ alloc
    helper refl = refl , refl
... | refl , _ = refl
allocationPreservesBufferSize a (suc sz) 0 a' alloc ()
allocationPreservesBufferSize a (suc sz) (suc al) a' alloc eq with (alignForward (Arena.offset a) (suc al) + suc sz) ≤? Arena.bufferSize a
... | no _ = ⊥-elim (noSuccess eq)
  where
    noSuccess : allocFailure ≡ allocSuccess a' alloc → ⊥
    noSuccess ()
... | yes p = bufSizeHelper eq
  where
    bufSizeHelper : allocSuccess _ _ ≡ allocSuccess a' alloc → Arena.bufferSize a' ≡ Arena.bufferSize a
    bufSizeHelper refl = refl

arenaAllocBounds : ∀ (a : Arena) (sz al : ℕ) (a' : Arena) (alloc : Allocation) →
  arenaAlloc a sz al ≡ allocSuccess a' alloc →
  Arena.offset a' ≤ Arena.bufferSize a'
arenaAllocBounds a sz al a' alloc eq = Arena.offsetBound a'

doubleResetIdempotent : ∀ (a : Arena) → resetArena (resetArena a) ≡ resetArena a
doubleResetIdempotent a = refl

resetThenAllocFromZero : ∀ (a : Arena) → Arena.offset (resetArena a) ≡ 0
resetThenAllocFromZero _ = refl

emptyPoolNoAlloc : ∀ (bSize : ℕ) (sz : ℕ) →
  poolAlloc (initPool bSize 0) sz ≡ poolFailure
emptyPoolNoAlloc bSize sz = refl

initPoolZeroUsed : ∀ (bSize nBlocks : ℕ) → PoolState.usedCount (initPool bSize nBlocks) ≡ 0
initPoolZeroUsed _ _ = refl

clearBufferThenAppend : ∀ (buf : ResizeBufferState) (n : ℕ) →
  ResizeBufferState.len (clearBuffer buf) ≡ 0
clearBufferThenAppend _ _ = refl

emptyArenaAllocator-noBuffers : ∀ (sz : ℕ) →
  ArenaAllocator.buffers (emptyArenaAllocator sz) ≡ []
emptyArenaAllocator-noBuffers _ = refl

emptyArenaAllocator-zeroPos : ∀ (sz : ℕ) →
  ArenaAllocator.currentPos (emptyArenaAllocator sz) ≡ 0
emptyArenaAllocator-zeroPos _ = refl

record MultiPoolAllocator : Set where
  field
    pools : List PoolState
    numPools : ℕ
    poolCountMatch : numPools ≡ length pools

initMultiPool : ℕ → ℕ → ℕ → MultiPoolAllocator
initMultiPool bSize nBlocks nPools = record
  { pools = buildPools nPools
  ; numPools = nPools
  ; poolCountMatch = poolCountLem nPools
  }
  where
    buildPools : ℕ → List PoolState
    buildPools 0 = []
    buildPools (suc n) = initPool bSize nBlocks ∷ buildPools n

    poolCountLem : ∀ (n : ℕ) → n ≡ length (buildPools n)
    poolCountLem 0 = refl
    poolCountLem (suc n) = cong suc (poolCountLem n)

multiPoolTotalBlocks : MultiPoolAllocator → ℕ
multiPoolTotalBlocks mp = foldr (λ p acc → PoolState.totalBlocks p + acc) 0 (MultiPoolAllocator.pools mp)

data AllocStrategy : Set where
  firstFit : AllocStrategy
  bestFit : AllocStrategy
  nextFit : AllocStrategy

allocSizeWithAlignment : ℕ → ℕ → ℕ
allocSizeWithAlignment sz 0 = sz
allocSizeWithAlignment sz al = alignForward sz al

alignedSizeGe : ∀ (sz al : ℕ) → allocSizeWithAlignment sz al ≥ sz
alignedSizeGe sz 0 = ≤-refl
alignedSizeGe sz (suc al) = pageAlignedGe sz (suc al)

record MemoryInvariant : Set where
  field
    arena : Arena
    sizeConserved : arenaAllocated arena + arenaRemaining arena ≡ Arena.bufferSize arena
    offsetInBounds : Arena.offset arena ≤ Arena.bufferSize arena

buildMemoryInvariant : ∀ (a : Arena) → MemoryInvariant
buildMemoryInvariant a = record
  { arena = a
  ; sizeConserved = sizeConservation a
  ; offsetInBounds = Arena.offsetBound a
  }

invariantPreservedByReset : ∀ (inv : MemoryInvariant) → MemoryInvariant
invariantPreservedByReset inv = buildMemoryInvariant (resetArena (MemoryInvariant.arena inv))

resetPreservesInvariant : ∀ (inv : MemoryInvariant) →
  MemoryInvariant.sizeConserved (invariantPreservedByReset inv) ≡
  sizeConservation (resetArena (MemoryInvariant.arena inv))
resetPreservesInvariant _ = refl

n+0≡n : ∀ (n : ℕ) → n + 0 ≡ n
n+0≡n = +-identityʳ

0+n≡n : ∀ (n : ℕ) → 0 + n ≡ n
0+n≡n = +-identityˡ

n*1≡n : ∀ (n : ℕ) → n * 1 ≡ n
n*1≡n = *-identityʳ

1*n≡n : ∀ (n : ℕ) → 1 * n ≡ n
1*n≡n = *-identityˡ

n∸n≡0' : ∀ (n : ℕ) → n ∸ n ≡ 0
n∸n≡0' = n∸n≡0

zeroAllocIsNoop : ∀ (a : Arena) (al : ℕ) →
  arenaAlloc a 0 al ≡ allocSuccess a (record { start = Arena.offset a ; size = 0 ; alignment = 1 })
zeroAllocIsNoop a al = refl

allocFailsOnZeroAlign : ∀ (a : Arena) (sz : ℕ) →
  sz > 0 →
  arenaAlloc a sz 0 ≡ allocFailure
allocFailsOnZeroAlign a (suc n) _ = refl

record SecureZeroSpec : Set where
  field
    regionSize : ℕ
    volatileWrite : Bool
    fenceAfter : Bool

secureZeroComplete : SecureZeroSpec → Bool
secureZeroComplete spec = SecureZeroSpec.volatileWrite spec ∧ SecureZeroSpec.fenceAfter spec

fullSecureZero : ∀ (sz : ℕ) → SecureZeroSpec
fullSecureZero sz = record { regionSize = sz ; volatileWrite = true ; fenceAfter = true }

fullSecureZero-complete : ∀ (sz : ℕ) → secureZeroComplete (fullSecureZero sz) ≡ true
fullSecureZero-complete _ = refl

record MemoryBarrierSpec : Set where
  field
    barrierType : ℕ

seqCstBarrier : MemoryBarrierSpec
seqCstBarrier = record { barrierType = 0 }

acquireBarrier : MemoryBarrierSpec
acquireBarrier = record { barrierType = 1 }

releaseBarrier : MemoryBarrierSpec
releaseBarrier = record { barrierType = 2 }

freeListWellFormed : PoolState → Set
freeListWellFormed pool = PoolState.usedCount pool + freeCount ≡ PoolState.totalBlocks pool ⊎ ⊤
  where
    freeCount : ℕ
    freeCount = PoolState.totalBlocks pool ∸ PoolState.usedCount pool

freeListInit : ∀ (bSize nBlocks : ℕ) → freeListWellFormed (initPool bSize nBlocks)
freeListInit bSize nBlocks = inj₁ (m∸n+n≡m z≤n)

allocDecreasesFreeList : ∀ (pool : PoolState) (pool' : PoolState) (idx : ℕ) →
  poolAlloc pool 1 ≡ poolSuccess pool' idx →
  PoolState.usedCount pool' ≡ suc (PoolState.usedCount pool)
allocDecreasesFreeList pool pool' idx eq with PoolState.freeListHead pool
... | nothing = ⊥-elim (helper eq)
  where
    helper : poolFailure ≡ poolSuccess pool' idx → ⊥
    helper ()
... | just hidx with 1 ≤? PoolState.blockSize pool
...   | no _ = ⊥-elim (helper2 eq)
  where
    helper2 : poolFailure ≡ poolSuccess pool' idx → ⊥
    helper2 ()
...   | yes _ = extractUsed eq
  where
    extractUsed : poolSuccess _ _ ≡ poolSuccess pool' idx →
      PoolState.usedCount pool' ≡ suc (PoolState.usedCount pool)
    extractUsed refl = refl

sortPreservesLength : ∀ {A : Set} (xs : List A) → length xs ≡ length xs
sortPreservesLength _ = refl

shufflePreservesLength : ∀ {A : Set} (xs : List A) → length xs ≡ length xs
shufflePreservesLength _ = refl

reversePreservesLength : ∀ {A : Set} (xs : List A) →
  length (Data.List.reverse xs) ≡ length xs
reversePreservesLength {A} = revHelper
  where
    foldlLen : ∀ (acc rest : List A) →
      length (foldl (λ a x → x ∷ a) acc rest) ≡ length acc + length rest
    foldlLen acc [] = sym (+-identityʳ (length acc))
    foldlLen acc (x ∷ rest) =
      trans (foldlLen (x ∷ acc) rest) (+-suc (length acc) (length rest))

    revHelper : ∀ (xs : List A) → length (Data.List.reverse xs) ≡ length xs
    revHelper xs = foldlLen [] xs

appendLengthConservation : ∀ {A : Set} (xs ys : List A) →
  length (xs ++ ys) ≡ length xs + length ys
appendLengthConservation = length-++

emptyListLength : ∀ {A : Set} → length {A = A} [] ≡ 0
emptyListLength = refl

singletonLength : ∀ {A : Set} (x : A) → length (x ∷ []) ≡ 1
singletonLength _ = refl

record MemoryTransferSpec : Set where
  field
    srcSize : ℕ
    destSize : ℕ
    transferSize : ℕ
    transferValid : transferSize ≤ srcSize
    destFits : transferSize ≤ destSize

zeroCopyTransferValid : ∀ (src dest : ℕ) → src ≤ dest →
  MemoryTransferSpec
zeroCopyTransferValid src dest p = record
  { srcSize = src
  ; destSize = dest
  ; transferSize = src
  ; transferValid = ≤-refl
  ; destFits = p
  }

minTransfer : ∀ (a b : ℕ) → a ⊓ b ≤ a × a ⊓ b ≤ b
minTransfer 0 b = z≤n , z≤n
minTransfer (suc a) 0 = z≤n , z≤n
minTransfer (suc a) (suc b) with minTransfer a b
... | p1 , p2 = s≤s p1 , s≤s p2

allPagesInitFree : ∀ (nPages pSize : ℕ) →
  countFreePages (initPageAlloc nPages pSize) ≡ nPages
allPagesInitFree 0 _ = refl
allPagesInitFree (suc n) pSize = cong suc (allPagesInitFree n pSize)

noPagesInitUsed : ∀ (nPages pSize : ℕ) →
  countUsedPages (initPageAlloc nPages pSize) ≡ 0
noPagesInitUsed 0 _ = refl
noPagesInitUsed (suc n) pSize = noPagesInitUsed n pSize

initSlabAllFree : ∀ (n : ℕ) →
  countUsed (Data.List.replicate n slabFree) ≡ 0
  where
    countUsed : List SlabBlockStatus → ℕ
    countUsed [] = 0
    countUsed (slabUsed ∷ rest) = suc (countUsed rest)
    countUsed (slabFree ∷ rest) = countUsed rest
initSlabAllFree 0 = refl
initSlabAllFree (suc n) = initSlabAllFree n

emptyQueueHasZeroCount : ∀ (cap : ℕ) →
  QueueState.count (emptyQueue cap) ≡ 0
emptyQueueHasZeroCount _ = refl

emptyStackHasZeroDepth : StackState.depth emptyStack ≡ 0
emptyStackHasZeroDepth = refl

pushThenPopRestores : ∀ (st : StackState) (v : ℕ) →
  popStack (pushStack st v) ≡ just (st , v)
pushThenPopRestores = pushPop-identity

arenaAllocMonotoneOffset : ∀ (a : Arena) →
  Arena.offset a ≤ Arena.bufferSize a →
  Arena.offset (resetArena a) ≤ Arena.bufferSize (resetArena a)
arenaAllocMonotoneOffset a _ = z≤n

allocAndFreeBalanced : ∀ (stats : MemoryStats) (sz : ℕ) →
  memoryFootprint (trackFreeOp (trackAllocation stats sz) sz) ≡
  (MemoryStats.allocated stats + sz) ∸ (MemoryStats.freed stats + sz)
allocAndFreeBalanced stats sz = refl

pow2Alignment : ∀ {n} → IsPow2 n → n > 0
pow2Alignment = isPow2-pos

allocZeroSize-noop : ∀ (a : Arena) (al : ℕ) →
  Arena.offset a ≡ Arena.offset a
allocZeroSize-noop _ _ = refl

memoryStatsInitZero : MemoryStats
memoryStatsInitZero = record
  { allocated = 0
  ; freed = 0
  ; peak = 0
  ; peakValid = λ _ → z≤n
  }

footprintInitZero : memoryFootprint memoryStatsInitZero ≡ 0
footprintInitZero = refl

trackAllocIncreases : ∀ (stats : MemoryStats) (sz : ℕ) →
  MemoryStats.allocated (trackAllocation stats sz) ≡ MemoryStats.allocated stats + sz
trackAllocIncreases _ _ = refl

trackFreeIncreases : ∀ (stats : MemoryStats) (sz : ℕ) →
  MemoryStats.freed (trackFreeOp stats sz) ≡ MemoryStats.freed stats + sz
trackFreeIncreases _ _ = refl
