/*
    Copyright (C) 2023 MrSpike63

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Affero General Public License as published by
    the Free Software Foundation, version 3.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Affero General Public License for more details.

    You should have received a copy of the GNU Affero General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

#pragma once
#include "curve_math.h"
#include "keccak.h"
#include "math.h"

__device__ void increment_random_bits_in_salt(_uint256* salt, int prefix_bits) {
    // Calculate mask for random bits
    _uint256 mask = create_random_bits_mask(prefix_bits);

    // Increment the random bits portion
    *salt = cpu_add_256_with_mask(*salt, _uint256{0,0,0,0,0,0,0,1}, mask);
}

__device__ _uint256 create_random_bits_mask(int prefix_bits) {
    _uint256 mask = {0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF,
                     0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF};

    int full_words = prefix_bits / 32;
    int remaining_bits = prefix_bits % 32;

    // Zero out the prefix bits
    for (int i = 0; i < full_words; i++) {
        ((uint32_t*)&mask)[i] = 0;
    }
    if (remaining_bits > 0 && full_words < 8) {
        ((uint32_t*)&mask)[full_words] &= (0xFFFFFFFF >> remaining_bits);
    }

    return mask;
}

__device__ _uint256 cpu_add_256_with_mask(_uint256 a, _uint256 b, _uint256 mask) {
    // Add 'b' to 'a' only where mask bits are set
    _uint256 result;
    uint64_t carry = 0;
    for (int i = 7; i >= 0; i--) {
        uint64_t sum = (uint64_t)(((uint32_t*)&a)[i] & mask_value(mask, i)) + (((uint32_t*)&b)[i] & mask_value(mask, i)) + carry;
        ((uint32_t*)&result)[i] = (uint32_t)(sum & 0xFFFFFFFF);
        carry = sum >> 32;
    }
    return result;
}

__device__ uint32_t mask_value(_uint256 mask, int index) {
    return ((uint32_t*)&mask)[index];
}



__global__ void __launch_bounds__(BLOCK_SIZE, 2) gpu_contract2_address_work(
    int score_method, Address a, _uint256 prefix_uint256, int prefix_bits,
    _uint256 base_random_key, _uint256 bytecode) {

    uint64_t thread_id = (uint64_t)threadIdx.x + (uint64_t)blockIdx.x * (uint64_t)BLOCK_SIZE;
    uint64_t key_offset = (uint64_t)THREAD_WORK * thread_id;

    _uint256 key = base_random_key;
    asm(
        "add.cc.u32 %0, %0, %8;     \n\t"
        "addc.cc.u32 %1, %1, %9;    \n\t"
        "addc.cc.u32 %2, %2, 0x0;   \n\t"
        "addc.cc.u32 %3, %3, 0x0;   \n\t"
        "addc.cc.u32 %4, %4, 0x0;   \n\t"
        "addc.cc.u32 %5, %5, 0x0;   \n\t"
        "addc.cc.u32 %6, %6, 0x0;   \n\t"
        "addc.u32 %7, %7, 0x0;      \n\t"
        : "+r"(key.h), "+r"(key.g), "+r"(key.f), "+r"(key.e), "+r"(key.d), "+r"(key.c), "+r"(key.b), "+r"(key.a)
        : "r"((uint32_t)(key_offset & 0xFFFFFFFF)), "r"((uint32_t)(key_offset >> 32))
    );

    int random_bits = 256 - prefix_bits;

    for (int i = 0; i < THREAD_WORK; i++) {
        // Shift key to align random bits after the prefix
        _uint256 shifted_random_bits = cpu_shift_left_256(key, prefix_bits);

        // Combine prefix and shifted random bits to form the full salt
        _uint256 salt = cpu_or_256(prefix_uint256, shifted_random_bits);

        // Compute the contract address using the salt
        Address addr = calculate_contract_address2(a, salt, bytecode);

        // Call handle_output2 with the salt
        handle_output2(score_method, addr, salt);

        // Increment key for the next iteration
        key.h += 1;
    }
}

